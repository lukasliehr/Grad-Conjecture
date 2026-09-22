import QuotientDerivativeL2
import ProductCoreConstruction

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.AnalyticWeights.Higher

def partialWordConstant (rank : ℕ) : ℝ :=
  1 + ∑ selected : Finset (Fin rank), profileConstant (selected.card + 1)

theorem partialWordConstant_nonnegative (rank : ℕ) : 0 ≤ partialWordConstant rank :=
  add_nonneg zero_le_one (Finset.sum_nonneg (fun _ _ => profileConstant_nonnegative _))

def partialGradeConstant (grade : ℕ) : ℝ :=
  ∑ index : GradeMultiIndex grade, partialWordConstant (cartesianOrder index.toCartesian)

theorem partialGradeConstant_nonnegative (grade : ℕ) : 0 ≤ partialGradeConstant grade :=
  Finset.sum_nonneg (fun _ _ => partialWordConstant_nonnegative _)

theorem partial_word_majorant {dimension rank : ℕ} (parameters : PhaseParameters)
    (direction : Fin 2) (field : ACore parameters dimension)
    (grade : ℕ) (word : CartesianWord rank) (rankBound : rank ≤ grade) :
    ∃ majorant : lp (fun _ : ℤ => ℝ) 2,
      (∀ cell, 0 ≤ majorant cell) ∧
      (∀ cell, cellFrequency cell ^ (grade - rank) *
        ‖closedContinuousToDiskL2 (closedDerivative
          (phaseWeightedJet parameters cell (partialJet direction (field.val cell))) rank word)‖ ≤ majorant cell) ∧
      ‖majorant‖ ≤ partialWordConstant rank * originalGradeNorm (grade + 1) field := by
  classical
  let leading := weightedWordL2Sequence parameters field (Fin.append word (fun _ : Fin 1 => direction))
    (grade - rank)
  let terms : Finset (Fin rank) → lp (fun _ : ℤ => ℝ) 2 := fun selected =>
    profileConstant (selected.card + 1) •
      weightedWordL2Sequence parameters field (subword word selectedᶜ) (grade + 1 - selectedᶜ.card)
  have cardBound (selected : Finset (Fin rank)) : selectedᶜ.card ≤ grade + 1 := by
    have bound := Finset.card_le_univ selectedᶜ
    rw [Fintype.card_fin] at bound
    omega
  have complement (selected : Finset (Fin rank)) : selected.card + selectedᶜ.card = rank := by
    have equality := selected.card_add_card_compl
    rw [Fintype.card_fin] at equality
    exact equality
  have leadingBound : ‖leading‖ ≤ originalGradeNorm (grade + 1) field := by
    have bound := weightedWordL2Sequence_norm_bound parameters field
      (Fin.append word (fun _ : Fin 1 => direction)) (grade - rank)
    convert bound using 1
    congr 1
    omega
  have termsNonnegative (selected : Finset (Fin rank)) (cell : ℤ) : 0 ≤ terms selected cell :=
    mul_nonneg (profileConstant_nonnegative _) (weightedWordL2Sequence_nonnegative _ _ _ _ _)
  have value (cell : ℤ) : (leading + ∑ selected, terms selected) cell =
      leading cell + ∑ selected, terms selected cell := by
    simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_sum, Finset.sum_apply]
  refine ⟨leading + ∑ selected, terms selected, ?_, ?_, ?_⟩
  · intro cell
    rw [value]
    exact add_nonneg (weightedWordL2Sequence_nonnegative _ _ _ _ _)
      (Finset.sum_nonneg (fun selected _ => termsNonnegative selected cell))
  · intro cell
    apply (mul_le_mul_of_nonneg_left (partialJet_weighted_L2 parameters cell direction (field.val cell) word)
      (pow_nonneg (cellFrequency_pos cell).le _)).trans_eq
    rw [value, mul_add, Finset.mul_sum]
    congr 1
    · exact (weightedWordL2Sequence_value parameters field _ _ cell).symm
    · apply Finset.sum_congr rfl
      intro selected _
      change _ = profileConstant (selected.card + 1) *
        weightedWordL2Sequence parameters field (subword word selectedᶜ) (grade + 1 - selectedᶜ.card) cell
      rw [weightedWordL2Sequence_value]
      have power : grade + 1 - selectedᶜ.card = grade - rank + (selected.card + 1) := by
        have := complement selected
        omega
      rw [power, pow_add]
      ring
  · calc
      _ ≤ ‖leading‖ + ∑ selected, ‖terms selected‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
      _ ≤ originalGradeNorm (grade + 1) field +
          ∑ selected : Finset (Fin rank),
            profileConstant (selected.card + 1) * originalGradeNorm (grade + 1) field := by
        apply add_le_add leadingBound
        apply Finset.sum_le_sum
        intro selected _
        change ‖profileConstant (selected.card + 1) •
          weightedWordL2Sequence parameters field (subword word selectedᶜ) (grade + 1 - selectedᶜ.card)‖ ≤ _
        rw [norm_smul, Real.norm_of_nonneg (profileConstant_nonnegative _)]
        have bound := weightedWordL2Sequence_norm_bound parameters field (subword word selectedᶜ)
          (grade + 1 - selectedᶜ.card)
        rw [Nat.add_sub_of_le (cardBound selected)] at bound
        exact mul_le_mul_of_nonneg_left bound (profileConstant_nonnegative _)
      _ = _ := by rw [← Finset.sum_mul]; simp only [partialWordConstant, add_mul, one_mul]

theorem partial_grade_majorant {dimension : ℕ} (parameters : PhaseParameters)
    (direction : Fin 2) (field : ACore parameters dimension) (grade : ℕ) :
    ∃ majorant : lp (fun _ : ℤ => ℝ) 2,
      (∀ cell, 0 ≤ majorant cell) ∧
      (∀ cell, ‖rawCartesianGradeCoordinates parameters grade
        (fun cell => partialJet direction (field.val cell)) cell‖ ≤ majorant cell) ∧
      ‖majorant‖ ≤ partialGradeConstant grade * originalGradeNorm (grade + 1) field := by
  classical
  choose majorants nonnegative pointBounds normBounds using
    (fun index : GradeMultiIndex grade => partial_word_majorant parameters direction field grade
      (cartesianMultiIndexWord index.toCartesian) index.property)
  have value (cell : ℤ) : (∑ index, majorants index) cell = ∑ index, majorants index cell := by
    simp only [lp.coeFn_sum, Finset.sum_apply]
  refine ⟨∑ index, majorants index, ?_, ?_, ?_⟩
  · intro cell
    rw [value]
    exact Finset.sum_nonneg (fun index _ => nonnegative index cell)
  · intro cell
    rw [value]
    apply finite_row_norm_le_majorants _ _ (fun index => nonnegative index cell)
    intro index
    change ‖(cellFrequency cell : ℂ) ^ (grade - cartesianOrder index.toCartesian) •
      closedContinuousToDiskL2 (closedMultiDerivative
        (phaseWeightedJet parameters cell (partialJet direction (field.val cell))) index.toCartesian)‖ ≤ _
    rw [norm_smul, Complex.norm_pow, Complex.norm_real, Real.norm_of_nonneg (cellFrequency_pos cell).le]
    exact pointBounds index cell
  · calc
      _ ≤ ∑ index, ‖majorants index‖ := norm_sum_le _ _
      _ ≤ ∑ index : GradeMultiIndex grade,
          partialWordConstant (cartesianOrder index.toCartesian) * originalGradeNorm (grade + 1) field :=
        Finset.sum_le_sum (fun index _ => normBounds index)
      _ = _ := by rw [← Finset.sum_mul]; rfl

theorem partial_mem_core {dimension : ℕ} (parameters : PhaseParameters)
    (direction : Fin 2) (field : ACore parameters dimension) :
    (fun cell => partialJet direction (field.val cell)) ∈ originalCoreSubmodule parameters dimension := by
  intro grade
  obtain ⟨majorant, nonnegative, bound, _⟩ := partial_grade_majorant parameters direction field grade
  apply (lp.memℓp majorant).mono'
  intro cell
  rw [Real.norm_of_nonneg (nonnegative cell)]
  exact bound cell

def partialCore {dimension : ℕ} (parameters : PhaseParameters) (direction : Fin 2) :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension where
  toFun field := ⟨fun cell => partialJet direction (field.val cell), partial_mem_core parameters direction field⟩
  map_add' first second := by
    apply Subtype.ext
    funext cell
    apply closedJet_eq_of_value_eq
    change closedDerivativeLinear 1 (fun _ => direction) (first.val cell + second.val cell) = _
    exact map_add _ _ _
  map_smul' scalar field := by
    apply Subtype.ext
    funext cell
    apply closedJet_eq_of_value_eq
    change closedDerivativeLinear 1 (fun _ => direction) (scalar • field.val cell) = _
    exact map_smul _ _ _

theorem partialCore_actual {dimension : ℕ} (parameters : PhaseParameters)
    (direction : Fin 2) (field : ACore parameters dimension) :
    IsActualPartial direction field (partialCore parameters direction field) := fun _ => rfl

theorem partialCore_bound {dimension : ℕ} (parameters : PhaseParameters)
    (direction : Fin 2) (field : ACore parameters dimension) (grade : ℕ) :
    originalGradeNorm grade (partialCore parameters direction field) ≤
      partialGradeConstant grade * originalGradeNorm (grade + 1) field := by
  obtain ⟨majorant, nonnegative, pointBounds, normBound⟩ := partial_grade_majorant parameters direction field grade
  apply le_trans _ normBound
  unfold originalGradeNorm
  rw [gradeCore_norm_eq_cartesianGradeSeminorm, cartesianGradeSeminorm_apply, gradeCoreCoordinates_apply]
  apply lp.norm_mono (by norm_num)
  intro cell
  rw [Real.norm_of_nonneg (nonnegative cell)]
  exact pointBounds cell

theorem actual_cartesian_derivative : CartesianDerivativeGoal := by
  refine ⟨partialGradeConstant, partialGradeConstant_nonnegative, ?_⟩
  intro parameters dimension direction
  exact ⟨partialCore parameters direction, partialCore_actual parameters direction,
    fun grade field => partialCore_bound parameters direction field grade⟩

end Grad.NonlinearQuotientBounds
