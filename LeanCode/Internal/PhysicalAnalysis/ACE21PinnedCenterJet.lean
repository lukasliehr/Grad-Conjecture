import ACE18ActualVolterraPoisson

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearRadial Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.NonlinearDivision (closedOrigin IsRotationInvariant laplacianJet)

/-- The literal value and both first Cartesian derivatives at the origin. -/
def CenterPinned {dimension : ℕ} (field : ClosedJet dimension) : Prop :=
  field.value closedOrigin = 0 ∧ ∀ direction : Fin 2, (partialJet direction field).value closedOrigin = 0

theorem volterraJet_origin {dimension : ℕ} (field : ClosedJet dimension) :
    (volterraJet field).value closedOrigin = 0 := by
  rw [volterraJet, radiusPowerJet_value]
  simp [radiusSquare, closedOrigin]

theorem volterraPower_succ_origin {dimension : ℕ} (count : ℕ) (field : ClosedJet dimension) :
    (volterraPower (count + 1) field).value closedOrigin = 0 := volterraJet_origin _

theorem volterraResolvent_origin {dimension : ℕ} (parameter : ℝ) (field : ClosedJet dimension) :
    (volterraResolventJet parameter field).value closedOrigin = 0 := by
  rw [volterraResolventJet_value]
  simp only [volterraPower_succ_origin, smul_zero, tsum_zero]

theorem centerSigned_origin {dimension : ℕ} (sign : ℝ) (field : ClosedJet dimension) :
    (coordinateMultiplyJet sign field).value closedOrigin = 0 := by
  rw [coordinateMultiplyJet_value]
  simp [signedComplexCoordinate, closedOrigin]

theorem centerSigned_partial_origin {dimension : ℕ} (sign : ℝ) (field : ClosedJet dimension) (direction : Fin 2) :
    (partialJet direction (coordinateMultiplyJet sign field)).value closedOrigin =
      (((spatialBasis direction 0 : ℝ) : ℂ) + Complex.I * (sign : ℂ) *
        ((spatialBasis direction 1 : ℝ) : ℂ)) • field.value closedOrigin := by
  simp only [centerCoordinate_decomposition, centerPartial_add, centerPartial_smul, centerPartial_coordinate]
  simp only [closedJet_value_add, ContinuousMap.add_apply, closedJet_value_smul, ContinuousMap.smul_apply,
    coordinateJet_value, closedOrigin, PiLp.zero_apply, zero_smul, add_zero, add_smul, mul_smul]

theorem centerSigned_pinned {dimension : ℕ} (sign : ℝ) (field : ClosedJet dimension)
    (origin : field.value closedOrigin = 0) : CenterPinned (coordinateMultiplyJet sign field) := by
  refine ⟨centerSigned_origin sign field, ?_⟩
  intro direction
  rw [centerSigned_partial_origin, origin, smul_zero]

theorem centerSigned_pinned_origin {dimension : ℕ} (sign : ℝ) (field : ClosedJet dimension)
    (pinned : CenterPinned (coordinateMultiplyJet sign field)) : field.value closedOrigin = 0 := by
  have identity := pinned.2 0
  rw [centerSigned_partial_origin] at identity
  simpa [spatialBasis] using identity

theorem centerResolvent_pinned {dimension : ℕ} (sign parameter : ℝ) (field : ClosedJet dimension) :
    CenterPinned (coordinateMultiplyJet sign (volterraResolventJet parameter field)) :=
  centerSigned_pinned sign _ (volterraResolvent_origin parameter field)

end Grad.ActualCenterVolterra
