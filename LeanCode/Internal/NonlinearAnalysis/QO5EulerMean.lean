import QO4ModeKernel
import RotationAverageDifferential

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped ContDiff Interval

namespace Grad.NonlinearRange

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.AxisSplit Grad.AxisJet Grad.QuotientProjection
open Grad.NonlinearQuotient Grad.PhysicalFamily Grad.GaugeCoefficients.Radial

variable {parameters : PhaseParameters}

def eulerJet {dimension : ℕ} (field : ClosedJet dimension) : ClosedJet dimension :=
  coordinateJet 0 (partialJet 0 field) + coordinateJet 1 (partialJet 1 field)

theorem partialJet_global_value {dimension : ℕ} (mapping : SpatialPlane → ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ mapping) (direction : Fin 2) (point : ClosedDisk) :
    (partialJet direction (globalClosedJet mapping smooth)).value point =
      fderiv ℝ mapping point.val (spatialBasis direction) := by
  change closedDerivative (globalClosedJet mapping smooth) 1 (fun _ => direction) point = _
  rw [globalClosedJet_derivative]
  simp only [cartesianDerivative, iteratedFDeriv_one_apply]

theorem eulerJet_global_value {dimension : ℕ} (mapping : SpatialPlane → ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ mapping) (point : ClosedDisk) :
    (eulerJet (globalClosedJet mapping smooth)).value point = fderiv ℝ mapping point.val point.val := by
  rw [eulerJet, closedJet_value_add, ContinuousMap.add_apply,
    coordinateJet_value, coordinateJet_value, partialJet_global_value, partialJet_global_value]
  conv_rhs => arg 2; rw [disk_basis_decomposition point.val]
  rw [map_add, map_smul, map_smul]
  rfl

theorem eulerJet_extension_value {dimension : ℕ} (field : ClosedJet dimension) (point : ClosedDisk) :
    (eulerJet field).value point = fderiv ℝ (smoothClosedExtension field) point.val point.val := by
  have equality := eulerJet_global_value (smoothClosedExtension field) (smoothClosedExtension_smooth field) point
  rw [smoothClosedExtension_restricts] at equality
  exact equality

theorem angularProjectionValue_zero_eq_average {dimension : ℕ}
    (mapping : SpatialPlane → ComplexEuclidean dimension) :
    angularProjectionValue 0 mapping = rotationAverage mapping := by
  funext point
  simp only [angularProjectionValue, rotationAverage, angularCharacter_zero_mode, one_smul]

/-- Radial differentiation commutes with the exact angular mean on the
closed Cartesian carrier. The proof uses the accepted smooth extension only
to calculate derivatives, and samples the original closed disk throughout. -/
theorem angularCore_eulerCore {dimension : ℕ} (field : ACore parameters dimension) :
    angularCore parameters 0 (eulerCore parameters field) =
      eulerCore parameters (angularCore parameters 0 field) := by
  apply Subtype.ext
  funext cell
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change (angularClosedJet 0 (eulerJet (field.val cell))).value point =
    (eulerJet (angularClosedJet 0 (field.val cell))).value point
  change (angularClosedJet 0 (eulerJet (field.val cell))).value point =
    (eulerJet (globalClosedJet (angularProjectionValue 0 (smoothClosedExtension (field.val cell)))
      (angularProjectionValue_smooth 0 (smoothClosedExtension_smooth (field.val cell))))).value point
  rw [eulerJet_global_value, angularProjectionValue_zero_eq_average,
    rotationAverage_euler (radius := 2) (smoothClosedExtension_smooth (field.val cell)).contDiffOn
      (show point.val ∈ Metric.ball (0 : SpatialPlane) 2 by
        rw [Metric.mem_ball, dist_zero_right]; exact point.property.trans_lt (by norm_num))]
  rw [angularClosedJet_value, rotationAverage]
  congr 1
  apply intervalIntegral.integral_congr
  intro angle _
  dsimp only
  rw [angularCharacter_zero_mode, one_smul, eulerJet_extension_value]
  simp only [physicalRotation_eq_orthogonal, planeRotationEquiv_apply]
  rfl

theorem angularCore_eulerCore_zero {dimension : ℕ} (field : ACore parameters dimension)
    (meanZero : angularCore parameters 0 field = 0) :
    angularCore parameters 0 (eulerCore parameters field) = 0 := by
  rw [angularCore_eulerCore, meanZero, map_zero]

end Grad.NonlinearRange
