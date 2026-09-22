import ACB1OriginalCenterSourceBound

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterBounds
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.ActualCenterVolterra
open Grad.NonlinearDivision (IsRotationInvariant)

theorem partial_radiusSquare_first {dimension : ℕ} (field : ClosedJet dimension) :
    partialJet 0 (radiusPowerJet 1 field) =
      coordinateJet 0 (shiftedEulerJet 1 field) - coordinateJet 1 (rotationJet field) := by
  simp only [radiusPower_one_decomposition, shiftedEulerJet, eulerJet, rotationJet,
    sub_eq_add_neg, centerPartial_add, centerPartial_coordinate,
    centerCoordinate_add, centerCoordinate_smul, centerCoordinate_neg]
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  simp [closedJet_value_add, closedJet_value_smul, closedJet_value_neg,
    coordinateJet_value, PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply,
    Complex.real_smul, spatialBasis]
  ring

theorem partial_radiusSquare_second {dimension : ℕ} (field : ClosedJet dimension) :
    partialJet 1 (radiusPowerJet 1 field) =
      coordinateJet 1 (shiftedEulerJet 1 field) + coordinateJet 0 (rotationJet field) := by
  simp only [radiusPower_one_decomposition, shiftedEulerJet, eulerJet, rotationJet,
    sub_eq_add_neg, centerPartial_add, centerPartial_coordinate,
    centerCoordinate_add, centerCoordinate_smul, centerCoordinate_neg]
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  simp [closedJet_value_add, closedJet_value_smul, closedJet_value_neg,
    coordinateJet_value, PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply,
    Complex.real_smul, spatialBasis]
  ring

theorem partial_radiusSquare_radial {dimension : ℕ} (direction : Fin 2)
    (field : ClosedJet dimension) (radial : IsRotationInvariant field) :
    partialJet direction (radiusPowerJet 1 field) = coordinateJet direction (shiftedEulerJet 1 field) := by
  have alternatives : direction = 0 ∨ direction = 1 := by omega
  rcases alternatives with rfl | rfl
  · simpa only [radial_rotation_zero field radial, centerCoordinate_zero, sub_zero] using partial_radiusSquare_first field
  · simpa only [radial_rotation_zero field radial, centerCoordinate_zero, add_zero] using partial_radiusSquare_second field

/-- The first Cartesian derivative of the actual radial Volterra operator
uses only values of its forcing. This avoids a source derivative loss. -/
theorem partial_volterra_radial {dimension : ℕ} (direction : Fin 2)
    (field : ClosedJet dimension) (radial : IsRotationInvariant field) :
    partialJet direction (volterraJet field) = coordinateJet direction (powerDilationJet 3 field) := by
  change partialJet direction (radiusPowerJet 1 (powerDilationJet 1 (powerDilationJet 3 field))) = _
  rw [partial_radiusSquare_radial direction _ (powerDilation_radial 1 _ (powerDilation_radial 3 field radial)),
    shiftedEuler_powerDilation]

end Grad.ActualCenterBounds
