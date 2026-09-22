import QuotientCoordinateJet
import QuotientLaplacian

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.AnalyticWeights.Higher

def coordinateWordConstant (rank : ℕ) : ℝ := Fintype.card (Finset (Fin rank))

def coordinateGradeConstant (grade : ℕ) : ℝ :=
  ∑ index : GradeMultiIndex grade, coordinateWordConstant (cartesianOrder index.toCartesian)

theorem coordinateGradeConstant_nonnegative (grade : ℕ) : 0 ≤ coordinateGradeConstant grade :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

theorem coordinate_word_majorant {dimension rank : ℕ} (parameters : PhaseParameters)
    (coordinate : Fin 2) (field : ACore parameters dimension)
    (grade : ℕ) (word : CartesianWord rank) (rankBound : rank ≤ grade) :
    ∃ majorant : lp (fun _ : ℤ => ℝ) 2,
      (∀ cell, 0 ≤ majorant cell) ∧
      (∀ cell, cellFrequency cell ^ (grade - rank) *
        ‖closedContinuousToDiskL2 (closedDerivative
          (phaseWeightedJet parameters cell (coordinateJet coordinate (field.val cell))) rank word)‖ ≤ majorant cell) ∧
      ‖majorant‖ ≤ coordinateWordConstant rank * originalGradeNorm grade field := by
  classical
  let terms : Finset (Fin rank) → lp (fun _ : ℤ => ℝ) 2 := fun selected =>
    weightedWordL2Sequence parameters field (subword word selectedᶜ) (grade - rank)
  have termsNonnegative (selected : Finset (Fin rank)) (cell : ℤ) : 0 ≤ terms selected cell :=
    weightedWordL2Sequence_nonnegative _ _ _ _ _
  have termsBound (selected : Finset (Fin rank)) : ‖terms selected‖ ≤ originalGradeNorm grade field := by
    apply (weightedWordL2Sequence_norm_bound parameters field (subword word selectedᶜ) (grade - rank)).trans
    apply cartesianGrade_norm_mono parameters
    have bound := Finset.card_le_univ selectedᶜ
    rw [Fintype.card_fin] at bound
    omega
  have value (cell : ℤ) : (∑ selected, terms selected) cell = ∑ selected, terms selected cell := by
    simp only [lp.coeFn_sum, Finset.sum_apply]
  refine ⟨∑ selected, terms selected, ?_, ?_, ?_⟩
  · intro cell
    rw [value]
    exact Finset.sum_nonneg (fun selected _ => termsNonnegative selected cell)
  · intro cell
    apply (mul_le_mul_of_nonneg_left (coordinateJet_weighted_L2 parameters cell coordinate (field.val cell) word)
      (pow_nonneg (cellFrequency_pos cell).le _)).trans_eq
    rw [value, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro selected _
    exact (weightedWordL2Sequence_value parameters field _ _ cell).symm
  · calc
      _ ≤ ∑ selected, ‖terms selected‖ := norm_sum_le _ _
      _ ≤ ∑ _selected : Finset (Fin rank), originalGradeNorm grade field :=
        Finset.sum_le_sum (fun selected _ => termsBound selected)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, coordinateWordConstant]

theorem coordinate_grade_majorant {dimension : ℕ} (parameters : PhaseParameters)
    (coordinate : Fin 2) (field : ACore parameters dimension) (grade : ℕ) :
    ∃ majorant : lp (fun _ : ℤ => ℝ) 2,
      (∀ cell, 0 ≤ majorant cell) ∧
      (∀ cell, ‖rawCartesianGradeCoordinates parameters grade
        (fun cell => coordinateJet coordinate (field.val cell)) cell‖ ≤ majorant cell) ∧
      ‖majorant‖ ≤ coordinateGradeConstant grade * originalGradeNorm grade field := by
  classical
  choose majorants nonnegative pointBounds normBounds using
    (fun index : GradeMultiIndex grade => coordinate_word_majorant parameters coordinate field grade
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
        (phaseWeightedJet parameters cell (coordinateJet coordinate (field.val cell))) index.toCartesian)‖ ≤ _
    rw [norm_smul, Complex.norm_pow, Complex.norm_real, Real.norm_of_nonneg (cellFrequency_pos cell).le]
    exact pointBounds index cell
  · calc
      _ ≤ ∑ index, ‖majorants index‖ := norm_sum_le _ _
      _ ≤ ∑ index : GradeMultiIndex grade,
          coordinateWordConstant (cartesianOrder index.toCartesian) * originalGradeNorm grade field :=
        Finset.sum_le_sum (fun index _ => normBounds index)
      _ = _ := by rw [← Finset.sum_mul]; rfl

theorem coordinate_mem_core {dimension : ℕ} (parameters : PhaseParameters)
    (coordinate : Fin 2) (field : ACore parameters dimension) :
    (fun cell => coordinateJet coordinate (field.val cell)) ∈ originalCoreSubmodule parameters dimension := by
  intro grade
  obtain ⟨majorant, nonnegative, bound, _⟩ := coordinate_grade_majorant parameters coordinate field grade
  apply (lp.memℓp majorant).mono'
  intro cell
  rw [Real.norm_of_nonneg (nonnegative cell)]
  exact bound cell

def coordinateCore {dimension : ℕ} (parameters : PhaseParameters) (coordinate : Fin 2) :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension where
  toFun field := ⟨fun cell => coordinateJet coordinate (field.val cell), coordinate_mem_core parameters coordinate field⟩
  map_add' first second := by
    apply Subtype.ext
    funext cell
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    change point.val coordinate • ((first.val cell).value point + (second.val cell).value point) =
      point.val coordinate • (first.val cell).value point + point.val coordinate • (second.val cell).value point
    exact smul_add _ _ _
  map_smul' scalar field := by
    apply Subtype.ext
    funext cell
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    change point.val coordinate • (scalar • (field.val cell).value point) =
      scalar • (point.val coordinate • (field.val cell).value point)
    exact smul_comm _ _ _

theorem coordinateCore_actual {dimension : ℕ} (parameters : PhaseParameters)
    (coordinate : Fin 2) (field : ACore parameters dimension) (cell : ℤ) (point : ClosedDisk) :
    ((coordinateCore parameters coordinate field).val cell).value point =
      point.val coordinate • (field.val cell).value point := rfl

theorem coordinateCore_bound {dimension : ℕ} (parameters : PhaseParameters)
    (coordinate : Fin 2) (field : ACore parameters dimension) (grade : ℕ) :
    originalGradeNorm grade (coordinateCore parameters coordinate field) ≤
      coordinateGradeConstant grade * originalGradeNorm grade field := by
  obtain ⟨majorant, nonnegative, pointBounds, normBound⟩ := coordinate_grade_majorant parameters coordinate field grade
  apply le_trans _ normBound
  unfold originalGradeNorm
  rw [gradeCore_norm_eq_cartesianGradeSeminorm, cartesianGradeSeminorm_apply, gradeCoreCoordinates_apply]
  apply lp.norm_mono (by norm_num)
  intro cell
  rw [Real.norm_of_nonneg (nonnegative cell)]
  exact pointBounds cell

end Grad.NonlinearQuotientBounds
