import ACE21PinnedCenterJet

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearRadial Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.NonlinearDivision (closedOrigin IsRotationInvariant laplacianJet)
open Grad.PhysicalFamily

theorem radiusPower_radial_reflect {dimension : ℕ} (field : ClosedJet dimension)
    (radial : IsRotationInvariant (radiusPowerJet 1 field)) : IsRotationInvariant field := by
  intro angle point
  by_cases axis : point.val = 0
  · have equality : Grad.NonlinearDivision.rotatedPoint angle point = point := by
      apply Subtype.ext
      change planeRotationAction angle point.val = point.val
      rw [axis, physicalRotation_eq_orthogonal]
      exact map_zero (Grad.GaugeCoefficients.Radial.planeRotationEquiv angle)
    rw [equality]
  · have nonzero : ‖point.val‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr axis)
    apply smul_right_injective (ComplexEuclidean dimension) nonzero
    have equality := radial angle point
    rw [radiusPowerJet_value, radiusPowerJet_value, pow_one, pow_one,
      radiusSquare_eq, radiusSquare_eq] at equality
    have sameNorm : ‖(Grad.NonlinearDivision.rotatedPoint angle point).val‖ = ‖point.val‖ :=
      physicalRotation_norm angle point.val
    rwa [sameNorm] at equality

def pinnedRadialQuotient {dimension : ℕ} (field : ClosedJet dimension) : ClosedJet dimension :=
  radialIntervalJet 0 1 (laplacianJet field)

/-- Smooth division of a pinned radial function by the actual squared
radius, using the accepted closed-disk radial division theorem. -/
theorem pinnedRadialQuotient_factor {dimension : ℕ} (field : ClosedJet dimension)
    (radial : IsRotationInvariant field) (origin : field.value closedOrigin = 0) :
    radiusPowerJet 1 (pinnedRadialQuotient field) = field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [radiusPowerJet_value, pow_one, radiusSquare_eq, pinnedRadialQuotient, radialIntervalJet_full_value]
  exact ((Grad.NonlinearDivision.actualRadialDivision dimension field radial origin).1 point).symm

theorem pinnedRadialQuotient_radial {dimension : ℕ} (field : ClosedJet dimension)
    (radial : IsRotationInvariant field) (origin : field.value closedOrigin = 0) :
    IsRotationInvariant (pinnedRadialQuotient field) := by
  apply radiusPower_radial_reflect
  rwa [pinnedRadialQuotient_factor field radial origin]

/-- The exact converse W5 under the center pin. This proves the integral
identity from the literal PDE, rather than assuming a singular ODE solution. -/
theorem pinnedRadial_volterra_inverse {dimension : ℕ} (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (field forcing : ClosedJet dimension) (radial : IsRotationInvariant field)
    (origin : field.value closedOrigin = 0)
    (equation : laplacianJet (coordinateMultiplyJet (mode : ℝ) field) =
      coordinateMultiplyJet (mode : ℝ) forcing) : field = volterraJet forcing := by
  have factor := pinnedRadialQuotient_factor field radial origin
  have radialQuotient := pinnedRadialQuotient_radial field radial origin
  have differential := centerLaplacian_radial mode center (pinnedRadialQuotient field) radialQuotient
  rw [factor] at differential
  have eulerEquation : shiftedEulerJet 1 (shiftedEulerJet 3 (pinnedRadialQuotient field)) = forcing :=
    centerCoordinate_injective mode center (differential.symm.trans equation)
  have integrated := congrArg (fun jet => powerDilationJet 3 (powerDilationJet 1 jet)) eulerEquation
  rw [powerDilation_shiftedEuler, powerDilation_shiftedEuler, powerDilation_commute 3 1] at integrated
  calc
    field = radiusPowerJet 1 (pinnedRadialQuotient field) := factor.symm
    _ = radiusPowerJet 1 (powerDilationJet 1 (powerDilationJet 3 forcing)) := congrArg (radiusPowerJet 1) integrated
    _ = volterraJet forcing := rfl

end Grad.ActualCenterVolterra
