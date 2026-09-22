import ACE13EulerPrimitiveIdentity

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearRadial Grad.NonlinearRange Grad.NonlinearQuotientBounds

theorem partial_powerDilation {dimension : ℕ} (power : ℕ) (direction : Fin 2) (field : ClosedJet dimension) :
    partialJet direction (powerDilationJet power field) = powerDilationJet (power + 1) (partialJet direction field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change closedDerivative (powerDilationJet power field) 1 (fun _ => direction) point = _
  rw [powerDilationJet_derivative, powerDilationJet_value]
  apply setIntegral_congr_fun measurableSet_Icc
  intro scale inside
  dsimp only
  congr 1
  have identity := smoothClosedExtension_value (partialJet direction field)
    (dilationPoint scale inside.1 inside.2 point)
  change smoothClosedExtension (partialJet direction field) (scale • point.val) =
    closedDerivative field 1 (fun _ => direction) (dilationPoint scale inside.1 inside.2 point) at identity
  rw [← smoothClosedExtension_derivative] at identity
  exact identity.symm

theorem powerDilation_coordinate {dimension : ℕ} (power : ℕ) (direction : Fin 2) (field : ClosedJet dimension) :
    powerDilationJet power (coordinateJet direction field) = coordinateJet direction (powerDilationJet (power + 1) field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [powerDilationJet_value, coordinateJet_value, powerDilationJet_value, ← integral_smul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro scale inside
  have identity := (smoothClosedExtension_value (coordinateJet direction field)
    (dilationPoint scale inside.1 inside.2 point)).trans
      (coordinateJet_value direction field (dilationPoint scale inside.1 inside.2 point))
  change smoothClosedExtension (coordinateJet direction field) (scale • point.val) =
    (scale • point.val) direction • field.value (dilationPoint scale inside.1 inside.2 point) at identity
  rw [← smoothClosedExtension_value field] at identity
  dsimp only
  rw [identity]
  simp only [PiLp.smul_apply, smul_eq_mul, pow_succ, smul_smul]
  congr 1
  ring

theorem powerDilation_euler {dimension : ℕ} (power : ℕ) (field : ClosedJet dimension) :
    powerDilationJet power (eulerJet field) = eulerJet (powerDilationJet power field) := by
  simp only [eulerJet, powerDilationJet_add, powerDilation_coordinate, partial_powerDilation]

theorem shiftedEuler_powerDilation {dimension : ℕ} (power : ℕ) (field : ClosedJet dimension) :
    shiftedEulerJet power (powerDilationJet power field) = field := by
  have inverse := powerDilation_shiftedEuler power field
  simpa only [shiftedEulerJet, powerDilationJet_add, powerDilationJet_smul, powerDilation_euler] using inverse

end Grad.ActualCenterVolterra
