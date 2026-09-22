import AKDY2InverseEulerRadialFidelity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
open Set Filter MeasureTheory
open scoped ENNReal
namespace Grad.OriginalRadialRecovery
open Grad.OriginalTerminalAllocation Grad.OriginalCartesianTameEstimate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def eulerCombinationCost : List (ℕ × ℝ) → ℝ :=
  List.rec 0 (fun term _ previous => 2*(|term.2|+previous))

theorem eulerCombinationCost_nonnegative (terms : List (ℕ × ℝ)) :
    0≤eulerCombinationCost terms := by
  induction terms with
  | nil => exact le_rfl
  | cons term terms previous => exact mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) previous)

theorem eulerCombination_squareEnergy (lower : ℝ) (jets : ℕ → ℝ → E)
    (continuous : ∀ rank,ContinuousOn (jets rank) (Icc lower 1))
    (payment : ℝ) (paymentNonnegative : 0≤payment) (terms : List (ℕ × ℝ))
    (energy : ∀ term ∈ terms,
      (∫⁻ radius in Icc lower 1,ENNReal.ofReal (‖jets term.1 radius‖^2))≤ENNReal.ofReal (payment^2)) :
    (∫⁻ radius in Icc lower 1,ENNReal.ofReal (‖eulerCombination jets terms radius‖^2))≤
      ENNReal.ofReal ((eulerCombinationCost terms*payment)^2) := by
  induction terms with
  | nil => simp [eulerCombination,eulerCombinationCost]
  | cons term terms previous =>
      have tail := previous (fun tail member => energy tail (List.mem_cons_of_mem term member))
      have first := boundedScalar_squareEnergy lower (fun _ => term.2) (jets term.1) |term.2| payment
        (abs_nonneg _) (fun _ _ => le_of_eq (Real.norm_eq_abs _)) (energy term List.mem_cons_self)
      have assembled := twoInput_squareEnergy (volume.restrict (Icc lower 1))
        (eulerCombination jets (term::terms)) (fun radius => term.2 • jets term.1 radius)
        (eulerCombination jets terms)
        (((continuous term.1).const_smul term.2).aestronglyMeasurable measurableSet_Icc)
        ((eulerCombination_continuousOn (Icc lower 1) jets continuous terms).aestronglyMeasurable measurableSet_Icc)
        1 1 (|term.2| *payment) (eulerCombinationCost terms*payment)
        (by norm_num) (by norm_num) (mul_nonneg (abs_nonneg _) paymentNonnegative)
        (mul_nonneg (eulerCombinationCost_nonnegative terms) paymentNonnegative)
        (Filter.Eventually.of_forall (fun radius => by
          change ‖term.2 • jets term.1 radius+eulerCombination jets terms radius‖≤_
          simpa only [one_mul] using norm_add_le (term.2 • jets term.1 radius) (eulerCombination jets terms radius))) first tail
      exact assembled.trans_eq (by congr 1; dsimp only [eulerCombinationCost]; ring)

/-- A finite constant depending only on the fixed positive collar and rank. -/
def rawRadialEnergyConstant (lower : ℝ) (rank : ℕ) : ℝ :=
  (lower⁻¹)^rank * eulerCombinationCost (inverseEulerTerms rank)

theorem rawRadialEnergyConstant_nonnegative (lower : ℝ) (positive : 0<lower) (rank : ℕ) :
    0≤rawRadialEnergyConstant lower rank :=
  mul_nonneg (pow_nonneg (inv_nonneg.mpr positive.le) _) (eulerCombinationCost_nonnegative _)

/-- Every ordinary radial jet is paid by finitely many Euler jet energies
on the SAME positive closed collar. No phase, width or domain is changed. -/
theorem radialTower_squareEnergy (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (jets : ℕ → ℝ → E) (continuous : ∀ rank,ContinuousOn (jets rank) (Icc lower 1))
    (derivative : ∀ order radius,radius∈Icc lower 1 → HasDerivWithinAt (jets order)
      (radius⁻¹ • jets (order+1) radius) (Icc lower 1) radius)
    (rank : ℕ) (payment : ℝ) (paymentNonnegative : 0≤payment)
    (energy : ∀ order,order≤rank →
      (∫⁻ radius in Icc lower 1,ENNReal.ofReal (‖jets order radius‖^2))≤ENNReal.ofReal (payment^2)) :
    (∫⁻ radius in Icc lower 1,ENNReal.ofReal (‖iteratedDerivWithin rank (jets 0) (Icc lower 1) radius‖^2))≤
      ENNReal.ofReal ((rawRadialEnergyConstant lower rank*payment)^2) := by
  have finiteEnergy := eulerCombination_squareEnergy lower jets continuous payment paymentNonnegative
    (inverseEulerTerms rank) (fun term member => energy term.1 (inverseEulerTerms_rank rank term member))
  have factorBound (radius : ℝ) (inside : radius∈Icc lower 1) :
      ‖(radius⁻¹)^rank‖≤(lower⁻¹)^rank := by
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (positive.le.trans inside.1)) _)]
    have inverseLe : radius⁻¹≤lower⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le positive inside.1
    exact pow_le_pow_left₀ (inv_nonneg.mpr (positive.le.trans inside.1)) inverseLe rank
  have paid := boundedScalar_squareEnergy lower (fun radius => (radius⁻¹)^rank)
    (eulerCombination jets (inverseEulerTerms rank)) ((lower⁻¹)^rank)
    (eulerCombinationCost (inverseEulerTerms rank)*payment)
    (pow_nonneg (inv_nonneg.mpr positive.le) _) factorBound finiteEnergy
  have same := inverseRadialJet_fidelity (Icc lower 1) (uniqueDiffOn_Icc bounded)
    (fun radius inside => (positive.trans_le inside.1).ne') jets derivative rank
  have identity :
      (∫⁻ radius in Icc lower 1,ENNReal.ofReal (‖iteratedDerivWithin rank (jets 0) (Icc lower 1) radius‖^2))=
      ∫⁻ radius in Icc lower 1,ENNReal.ofReal (‖inverseRadialJet jets rank radius‖^2) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
    rw [same inside]
  rw [identity]
  exact paid.trans_eq (by rw [rawRadialEnergyConstant,mul_assoc])

end Grad.OriginalRadialRecovery
