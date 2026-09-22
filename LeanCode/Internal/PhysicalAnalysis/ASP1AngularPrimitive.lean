import ARW10UniformOuterGain
import ABF3ActualFiniteSmoothInverse
import QO5EulerMean

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.ActualSmoothPDE
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.GaugeCoefficients.Radial Grad.PhysicalFamily

theorem cartesianRotation_smooth : ContDiff ℝ ∞
    (fun argument : SpatialPlane × ℝ => planeRotationAction argument.2 argument.1) := by
  rw [contDiff_piLp]
  intro coordinate
  fin_cases coordinate <;>
    simp [planeRotationAction, Grad.GeometryClosure.planarRotation, Matrix.vecHead, Matrix.vecTail] <;>
    fun_prop

/-- Compact Cartesian rotation integral: there is no singular division at the axis. -/
def weightedRotationValue (weight : ℝ → ℝ) (field : SpatialPlane → ComplexEuclidean 1)
    (point : SpatialPlane) : ComplexEuclidean 1 :=
  (2 * Real.pi)⁻¹ • ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
    weight angle • field (planeRotationAction angle point)

theorem weightedRotationValue_smooth (weight : ℝ → ℝ) (weightSmooth : ContDiff ℝ ∞ weight)
    (field : SpatialPlane → ComplexEuclidean 1) (smooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ (weightedRotationValue weight field) := by
  have integrand : ContDiff ℝ ∞ (fun argument : SpatialPlane × ℝ =>
      weight argument.2 • field (planeRotationAction argument.2 argument.1)) :=
    (weightSmooth.comp contDiff_snd).smul
      (smooth.comp cartesianRotation_smooth)
  apply contDiffOn_univ.mp
  change ContDiffOn ℝ ∞ (fun point => (2 * Real.pi)⁻¹ • ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
    weight angle • field (planeRotationAction angle point)) univ
  exact (contDiffOn_const (c := ((2 * Real.pi)⁻¹ : ℝ))).smul
    (contDiffOn_compactIntegral isOpen_univ integrand.contDiffOn 0 (2 * Real.pi))

def weightedRotationJet (weight : ℝ → ℝ) (weightSmooth : ContDiff ℝ ∞ weight)
    (field : ClosedJet 1) : ClosedJet 1 :=
  globalClosedJet (weightedRotationValue weight (smoothClosedExtension field))
    (weightedRotationValue_smooth weight weightSmooth _ (smoothClosedExtension_smooth field))

theorem weightedRotationJet_value (weight : ℝ → ℝ) (weightSmooth : ContDiff ℝ ∞ weight)
    (field : ClosedJet 1) (point : ClosedDisk) :
    (weightedRotationJet weight weightSmooth field).value point =
      (2 * Real.pi)⁻¹ • ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
        weight angle • field.value (rotatedPoint angle point) := by
  change weightedRotationValue weight (smoothClosedExtension field) point.val = _
  unfold weightedRotationValue
  congr 1
  apply integral_congr_ae
  filter_upwards with angle
  have literal := smoothClosedExtension_value field (rotatedPoint angle point)
  simpa only [physicalRotation_eq_orthogonal, planeRotationEquiv_apply, rotatedPoint] using
    congrArg (fun value : ComplexEuclidean 1 => weight angle • value) literal

/-- On every nonzero angular mode this is R inverse, with R=∂θ. -/
def angularPrimitiveJet (field : ClosedJet 1) : ClosedJet 1 :=
  weightedRotationJet id contDiff_id field

theorem angularPrimitiveJet_value (field : ClosedJet 1) (point : ClosedDisk) :
    (angularPrimitiveJet field).value point =
      (2 * Real.pi)⁻¹ • ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
        angle • field.value (rotatedPoint angle point) :=
  weightedRotationJet_value id contDiff_id field point

end Grad.ActualSmoothPDE
