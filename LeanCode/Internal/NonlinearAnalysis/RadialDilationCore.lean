import RadialWeightedDerivative
import ProductCoreConstruction

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearRadial

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.AnalyticWeights.Higher

def dilationWordConstant (rank : ℕ) : ℝ :=
  ∑ selected : Finset (Fin rank), dilationDerivativeConstant selected.card

theorem dilationWordConstant_nonnegative (rank : ℕ) : 0 ≤ dilationWordConstant rank :=
  Finset.sum_nonneg (fun _ _ => dilationDerivativeConstant_nonnegative _)

def dilationGradeConstant (grade : ℕ) : ℝ :=
  ∑ index : GradeMultiIndex grade, dilationWordConstant (cartesianOrder index.toCartesian)

theorem dilationGradeConstant_nonnegative (grade : ℕ) : 0 ≤ dilationGradeConstant grade :=
  Finset.sum_nonneg (fun _ _ => dilationWordConstant_nonnegative _)

theorem dilation_word_majorant {dimension rank : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) {scale : ℝ} (positive : 0 < scale) (bounded : scale ≤ 1)
    (grade : ℕ) (word : CartesianWord rank) (rankBound : rank ≤ grade) :
    ∃ majorant : lp (fun _ : ℤ => ℝ) 2,
      (∀ cell, 0 ≤ majorant cell) ∧
      (∀ cell, cellFrequency cell ^ (grade - rank) *
        ‖closedContinuousToDiskL2 (closedDerivative
          (phaseWeightedJet parameters cell (dilationJet scale (field.val cell))) rank word)‖ ≤ majorant cell) ∧
      ‖majorant‖ ≤ dilationWordConstant rank * scale⁻¹ * originalGradeNorm grade field := by
  classical
  let terms : Finset (Fin rank) → lp (fun _ : ℤ => ℝ) 2 := fun selected =>
    (dilationDerivativeConstant selected.card * scale⁻¹) •
      weightedWordL2Sequence parameters field (subword word selectedᶜ) (grade - selectedᶜ.card)
  have cardBound (selected : Finset (Fin rank)) : selectedᶜ.card ≤ grade := by
    have bound := Finset.card_le_univ selectedᶜ
    rw [Fintype.card_fin] at bound
    exact bound.trans rankBound
  have complement (selected : Finset (Fin rank)) : selected.card + selectedᶜ.card = rank := by
    have equality := selected.card_add_card_compl
    rw [Fintype.card_fin] at equality
    exact equality
  have coefficientsNonnegative (selected : Finset (Fin rank)) :
      0 ≤ dilationDerivativeConstant selected.card * scale⁻¹ :=
    mul_nonneg (dilationDerivativeConstant_nonnegative _) (inv_nonneg.mpr positive.le)
  have termsNonnegative (selected : Finset (Fin rank)) (cell : ℤ) : 0 ≤ terms selected cell :=
    mul_nonneg (coefficientsNonnegative selected) (weightedWordL2Sequence_nonnegative _ _ _ _ _)
  have value (cell : ℤ) : (∑ selected, terms selected) cell = ∑ selected, terms selected cell := by
    simp only [lp.coeFn_sum, Finset.sum_apply]
  refine ⟨∑ selected, terms selected, ?_, ?_, ?_⟩
  · intro cell
    rw [value]
    exact Finset.sum_nonneg (fun selected _ => termsNonnegative selected cell)
  · intro cell
    apply (mul_le_mul_of_nonneg_left (weightedDilation_L2_bound parameters cell positive bounded
      (field.val cell) word) (pow_nonneg (cellFrequency_pos cell).le _)).trans_eq
    rw [value, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro selected _
    change _ = (dilationDerivativeConstant selected.card * scale⁻¹) *
      weightedWordL2Sequence parameters field (subword word selectedᶜ) (grade - selectedᶜ.card) cell
    rw [weightedWordL2Sequence_value]
    have power : grade - selectedᶜ.card = grade - rank + selected.card := by
      have := complement selected
      omega
    rw [power, pow_add]
    ring
  · calc
      _ ≤ ∑ selected, ‖terms selected‖ := norm_sum_le _ _
      _ ≤ ∑ selected : Finset (Fin rank),
          (dilationDerivativeConstant selected.card * scale⁻¹) * originalGradeNorm grade field := by
        apply Finset.sum_le_sum
        intro selected _
        change ‖(dilationDerivativeConstant selected.card * scale⁻¹) •
          weightedWordL2Sequence parameters field (subword word selectedᶜ) (grade - selectedᶜ.card)‖ ≤ _
        rw [norm_smul, Real.norm_of_nonneg (coefficientsNonnegative selected)]
        have bound := weightedWordL2Sequence_norm_bound parameters field (subword word selectedᶜ)
          (grade - selectedᶜ.card)
        rw [Nat.add_sub_of_le (cardBound selected)] at bound
        exact mul_le_mul_of_nonneg_left bound (coefficientsNonnegative selected)
      _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; rfl

theorem dilation_grade_majorant {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) {scale : ℝ} (positive : 0 < scale) (bounded : scale ≤ 1)
    (grade : ℕ) :
    ∃ majorant : lp (fun _ : ℤ => ℝ) 2,
      (∀ cell, 0 ≤ majorant cell) ∧
      (∀ cell, ‖rawCartesianGradeCoordinates parameters grade
        (fun cell => dilationJet scale (field.val cell)) cell‖ ≤ majorant cell) ∧
      ‖majorant‖ ≤ dilationGradeConstant grade * scale⁻¹ * originalGradeNorm grade field := by
  classical
  choose majorants nonnegative pointBounds normBounds using
    (fun index : GradeMultiIndex grade => dilation_word_majorant parameters field positive bounded grade
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
        (phaseWeightedJet parameters cell (dilationJet scale (field.val cell))) index.toCartesian)‖ ≤ _
    rw [norm_smul, Complex.norm_pow, Complex.norm_real, Real.norm_of_nonneg (cellFrequency_pos cell).le]
    exact pointBounds index cell
  · calc
      _ ≤ ∑ index, ‖majorants index‖ := norm_sum_le _ _
      _ ≤ ∑ index : GradeMultiIndex grade,
          dilationWordConstant (cartesianOrder index.toCartesian) * scale⁻¹ * originalGradeNorm grade field :=
        Finset.sum_le_sum (fun index _ => normBounds index)
      _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; rfl

theorem dilation_mem_core {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) {scale : ℝ} (positive : 0 < scale) (bounded : scale ≤ 1) :
    (fun cell => dilationJet scale (field.val cell)) ∈ originalCoreSubmodule parameters dimension := by
  intro grade
  obtain ⟨majorant, nonnegative, bound, _⟩ := dilation_grade_majorant parameters field positive bounded grade
  apply (lp.memℓp majorant).mono'
  intro cell
  rw [Real.norm_of_nonneg (nonnegative cell)]
  exact bound cell

def dilationCore {dimension : ℕ} (parameters : PhaseParameters)
    (scale : ℝ) (positive : 0 < scale) (bounded : scale ≤ 1)
    (field : ACore parameters dimension) : ACore parameters dimension :=
  ⟨fun cell => dilationJet scale (field.val cell), dilation_mem_core parameters field positive bounded⟩

theorem dilationCore_bound {dimension : ℕ} (parameters : PhaseParameters)
    (scale : ℝ) (positive : 0 < scale) (bounded : scale ≤ 1)
    (field : ACore parameters dimension) (grade : ℕ) :
    originalGradeNorm grade (dilationCore parameters scale positive bounded field) ≤
      dilationGradeConstant grade * scale⁻¹ * originalGradeNorm grade field := by
  obtain ⟨majorant, nonnegative, pointBounds, normBound⟩ :=
    dilation_grade_majorant parameters field positive bounded grade
  apply le_trans _ normBound
  unfold originalGradeNorm
  rw [gradeCore_norm_eq_cartesianGradeSeminorm, cartesianGradeSeminorm_apply, gradeCoreCoordinates_apply]
  apply lp.norm_mono (by norm_num)
  intro cell
  rw [Real.norm_of_nonneg (nonnegative cell)]
  exact pointBounds cell

def dilationCoreLinear {dimension : ℕ} (parameters : PhaseParameters)
    (scale : ℝ) (positive : 0 < scale) (bounded : scale ≤ 1) :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension where
  toFun := dilationCore parameters scale positive bounded
  map_add' first second := by
    apply Subtype.ext
    funext cell
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    change (dilationJet scale ((first + second).val cell)).value point =
      (dilationJet scale (first.val cell)).value point + (dilationJet scale (second.val cell)).value point
    simp only [dilationJet_value_closed positive.le bounded]
    rfl
  map_smul' scalar field := by
    apply Subtype.ext
    funext cell
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    change (dilationJet scale ((scalar • field).val cell)).value point =
      scalar • (dilationJet scale (field.val cell)).value point
    simp only [dilationJet_value_closed positive.le bounded]
    rfl

theorem actual_dilation : RadialDilationGoal := by
  refine ⟨dilationGradeConstant, dilationGradeConstant_nonnegative, ?_⟩
  intro parameters dimension scale positive bounded
  refine ⟨dilationCoreLinear parameters scale positive bounded, ?_, ?_⟩
  · intro field cell point
    rfl
  · intro grade field
    exact dilationCore_bound parameters scale positive bounded field grade

end Grad.NonlinearRadial
