import ACB18ActualGlobalGradeRecurrence

noncomputable section
set_option maxHeartbeats 1400000
open scoped BigOperators
namespace Grad.ActualCenterBounds
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.ActualCenterVolterra Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.RadialLedger (apLoweringConstant apLoweringConstant_nonnegative)

private theorem centerScalarGradeInduction {Input : Type*} (grade : ℕ)
    (energy : Input → ℕ → ℝ) (size : Input → ℝ) (base : ℝ) (state forcing : ℕ → ℝ)
    (baseNonnegative : 0 ≤ base) (stateNonnegative : ∀ order, 0 ≤ state order)
    (forcingNonnegative : ∀ order, 0 ≤ forcing order)
    (baseBound : ∀ input, energy input 1 ≤ base * size input)
    (stepBound : ∀ order, order ≤ grade → ∀ input,
      energy input (order + 2) ≤ state order * energy input (order + 1) + forcing order * size input) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ input, energy input (grade + 2) ≤ constant * size input := by
  have every : ∀ order : ℕ, order ≤ grade + 1 → ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ input, energy input (order + 1) ≤ constant * size input := by
    intro order
    induction order with
    | zero => exact fun _ => ⟨base, baseNonnegative, baseBound⟩
    | succ order previous =>
      intro upper
      obtain ⟨constant, nonnegative, bound⟩ := previous (by omega)
      refine ⟨state order * constant + forcing order,
        add_nonneg (mul_nonneg (stateNonnegative order) nonnegative) (forcingNonnegative order), ?_⟩
      intro input
      exact (stepBound order (by omega) input).trans
        ((add_le_add (mul_le_mul_of_nonneg_left (bound input) (stateNonnegative order)) le_rfl).trans_eq (by ring))
  exact every (grade + 1) le_rfl


/-- AN6c on the exact original ordinary Sobolev norms, with the source grade
s≥3 and a single constant chosen before the sign, frequency, and datum. -/
theorem actual_center_native_gain (grade : ℕ) (large : 3 ≤ grade) (radius : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (mode : ℤ), mode = 1 ∨ mode = -1 →
      ∀ (frequency : ℝ), |frequency| ≤ radius → ∀ (source : ClosedJet 1),
      angularClosedJet mode source = source →
      ‖unitDiskCoreInto (grade + 2) (pinnedCenterSolution mode frequency source)‖ ≤
        constant * ‖unitDiskCoreInto grade source‖ := by
  let energy (datum : NativeCenterDatum radius) (order : ℕ) :=
    ‖unitDiskCoreInto order (pinnedCenterSolution datum.mode datum.frequency datum.source)‖
  let size (datum : NativeCenterDatum radius) := ‖unitDiskCoreInto grade datum.source‖
  obtain ⟨constant, nonnegative, estimates⟩ := centerScalarGradeInduction grade energy size
    (centerH1Constant radius * apLoweringConstant 3)
    (fun order => centerGlobalStateConstant order radius) (centerGlobalSourceConstant grade large radius)
    (mul_nonneg (centerH1Constant_nonnegative radius) (apLoweringConstant_nonnegative 3))
    (fun order => centerGlobalStateConstant_nonnegative order radius)
    (centerGlobalSourceConstant_nonnegative grade large radius)
    (by
      intro datum
      have bound := (pinnedCenterSolution_H1 radius datum.mode datum.center datum.frequency datum.bounded datum.source datum.pure).trans
        (mul_le_mul_of_nonneg_left (originalCore_lower large datum.source) (centerH1Constant_nonnegative radius))
      exact bound.trans_eq (mul_assoc _ _ _).symm)
    (fun order paid datum => pinnedCenter_global_step grade large radius datum.mode datum.center datum.frequency
      datum.bounded datum.source datum.pure order paid)
  refine ⟨constant, nonnegative, ?_⟩
  intro mode center frequency bounded source pure
  exact estimates ⟨mode, center, frequency, bounded, source, pure⟩

def centerNativeGainConstant (grade : ℕ) (large : 3 ≤ grade) (radius : ℝ) : ℝ :=
  (actual_center_native_gain grade large radius).choose

theorem centerNativeGainConstant_nonnegative (grade : ℕ) (large : 3 ≤ grade) (radius : ℝ) :
    0 ≤ centerNativeGainConstant grade large radius := (actual_center_native_gain grade large radius).choose_spec.1

theorem pinnedCenterSolution_native_gain (grade : ℕ) (large : 3 ≤ grade) (radius : ℝ)
    (mode : ℤ) (center : mode = 1 ∨ mode = -1) (frequency : ℝ) (bounded : |frequency| ≤ radius)
    (source : ClosedJet 1) (pure : angularClosedJet mode source = source) :
    ‖unitDiskCoreInto (grade + 2) (pinnedCenterSolution mode frequency source)‖ ≤
      centerNativeGainConstant grade large radius * ‖unitDiskCoreInto grade source‖ :=
  (actual_center_native_gain grade large radius).choose_spec.2 mode center frequency bounded source pure

end Grad.ActualCenterBounds
