import ProductWordMajorant

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearProduct

open Grad.ClosedJets Grad.CartesianState

theorem finite_sum_squares_le_square_sum {Index : Type} (indices : Finset Index) (values : Index → ℝ)
    (nonnegative : ∀ index ∈ indices, 0 ≤ values index) :
    (∑ index ∈ indices, values index ^ 2) ≤ (∑ index ∈ indices, values index) ^ 2 := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices outside inductionHypothesis =>
    have oldNonnegative : ∀ other ∈ indices, 0 ≤ values other :=
      fun other membership => nonnegative other (Finset.mem_insert_of_mem membership)
    have oldBound := inductionHypothesis oldNonnegative
    have newNonnegative := nonnegative index (Finset.mem_insert_self _ _)
    have sumNonnegative := Finset.sum_nonneg oldNonnegative
    rw [Finset.sum_insert outside, Finset.sum_insert outside]
    nlinarith [mul_nonneg newNonnegative sumNonnegative]

theorem finite_row_norm_le_majorants {Index Value : Type} [Fintype Index]
    [NormedAddCommGroup Value] (row : PiLp 2 (fun _ : Index => Value))
    (majorants : Index → ℝ) (nonnegative : ∀ index, 0 ≤ majorants index)
    (dominated : ∀ index, ‖row index‖ ≤ majorants index) :
    ‖row‖ ≤ ∑ index, majorants index := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun index _ => nonnegative index))).mp
  rw [PiLp.norm_sq_eq_of_L2]
  exact (Finset.sum_le_sum (fun index _ => pow_le_pow_left₀ (norm_nonneg _) (dominated index) 2)).trans
    (finite_sum_squares_le_square_sum Finset.univ majorants (fun index _ => nonnegative index))

def productGradeBaseConstant (arity grade : ℕ) : ℝ :=
  ∑ index : GradeMultiIndex grade, productWordBaseConstant arity grade (cartesianMultiIndexWord index.toCartesian)

theorem productGradeBaseConstant_nonnegative (arity grade : ℕ) : 0 ≤ productGradeBaseConstant arity grade :=
  Finset.sum_nonneg (fun _ _ => productWordBaseConstant_nonnegative _ _ _)

def productGradeConstant (arity grade : ℕ) : ℝ :=
  productGradeBaseConstant arity grade * allocationInterpolationConstant grade ^ (arity + 1)

theorem productGradeConstant_nonnegative (arity grade : ℕ) : 0 ≤ productGradeConstant arity grade :=
  mul_nonneg (productGradeBaseConstant_nonnegative _ _)
    (pow_nonneg (zero_le_one.trans (allocationInterpolationConstant_one_le _)) _)

theorem product_grade_majorant_of_allocated_bound {arity outputDimension : ℕ} {dimensions : Fin (arity + 1) → ℕ}
    (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin (arity + 1)) → ACore parameters (dimensions index)) (grade : ℕ)
    (allocationBound : ℝ)
    (bounded : ∀ orders : Fin (arity + 1) → ℕ, (∑ index, orders index) = grade →
      allocatedNormProduct orders fields ≤ allocationBound) :
    ∃ majorant : lp (fun _ : ℤ => ℝ) 2,
      (∀ cell, 0 ≤ majorant cell) ∧
      (∀ cell, ‖rawCartesianGradeCoordinates parameters grade
        (productCoefficientJet (Nat.succ_pos arity) parameters multiplication fields) cell‖ ≤ majorant cell) ∧
      ‖majorant‖ ≤ productGradeBaseConstant arity grade * ‖multiplication‖ * allocationBound := by
  classical
  choose majorants nonnegative pointBounds normBounds using
    (fun index : GradeMultiIndex grade => product_word_majorant_of_allocated_bound parameters multiplication fields grade
      (cartesianMultiIndexWord index.toCartesian) index.property allocationBound bounded)
  let majorant : lp (fun _ : ℤ => ℝ) 2 := ∑ index, majorants index
  have majorantValue (cell : ℤ) : majorant cell = ∑ index, majorants index cell := by
    simp only [majorant, lp.coeFn_sum, Finset.sum_apply]
  refine ⟨majorant, ?_, ?_, ?_⟩
  · intro cell
    rw [majorantValue]
    exact Finset.sum_nonneg (fun index _ => nonnegative index cell)
  · intro cell
    rw [majorantValue]
    apply finite_row_norm_le_majorants _ _ (fun index => nonnegative index cell)
    intro index
    have bound := pointBounds index cell
    change ‖(cellFrequency cell : ℂ) ^ (grade - cartesianOrder index.toCartesian) •
      closedContinuousToDiskL2 (closedMultiDerivative
        (phaseWeightedJet parameters cell
          (productCoefficientJet (Nat.succ_pos arity) parameters multiplication fields cell)) index.toCartesian)‖ ≤ _
    rw [productCoefficientJet_weighted, norm_smul, Complex.norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (cellFrequency_pos cell).le]
    simpa only [norm_smul, Real.norm_of_nonneg (pow_nonneg (cellFrequency_pos cell).le _), closedMultiDerivative] using bound
  · calc
      _ ≤ ∑ index, ‖majorants index‖ := norm_sum_le _ _
      _ ≤ ∑ index : GradeMultiIndex grade,
          productWordBaseConstant arity grade (cartesianMultiIndexWord index.toCartesian) *
            ‖multiplication‖ * allocationBound := Finset.sum_le_sum (fun index _ => normBounds index)
      _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; rfl

theorem product_grade_majorant_exists {arity outputDimension : ℕ} {dimensions : Fin (arity + 1) → ℕ}
    (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin (arity + 1)) → ACore parameters (dimensions index)) (grade : ℕ) :
    ∃ majorant : lp (fun _ : ℤ => ℝ) 2,
      (∀ cell, 0 ≤ majorant cell) ∧
      (∀ cell, ‖rawCartesianGradeCoordinates parameters grade
        (productCoefficientJet (Nat.succ_pos arity) parameters multiplication fields) cell‖ ≤ majorant cell) ∧
      ‖majorant‖ ≤ productGradeConstant arity grade * ‖multiplication‖ * oneHighExpression grade fields := by
  obtain ⟨majorant, nonnegative, pointBound, normBound⟩ := product_grade_majorant_of_allocated_bound
    parameters multiplication fields grade
    (allocationInterpolationConstant grade ^ (arity + 1) * oneHighExpression grade fields)
    (fun orders total => (allocatedNormProduct_le_all_shifted orders fields).trans
      (original_allocated_product_all_grades (Nat.succ_pos arity) grade orders total fields))
  refine ⟨majorant, nonnegative, pointBound, normBound.trans_eq ?_⟩
  unfold productGradeConstant
  ring

/-- Q1: the literal convolution is in every original M2 grade. -/
theorem productCoefficientJet_mem_originalCore {arity outputDimension : ℕ}
    {dimensions : Fin (arity + 1) → ℕ} (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin (arity + 1)) → ACore parameters (dimensions index)) :
    productCoefficientJet (Nat.succ_pos arity) parameters multiplication fields ∈
      originalCoreSubmodule parameters outputDimension := by
  intro grade
  obtain ⟨majorant, nonnegative, bound, _⟩ := product_grade_majorant_exists parameters multiplication fields grade
  apply (lp.memℓp majorant).mono'
  intro cell
  rw [Real.norm_of_nonneg (nonnegative cell)]
  exact bound cell

def actualMultilinearProduct {arity outputDimension : ℕ} {dimensions : Fin (arity + 1) → ℕ}
    (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin (arity + 1)) → ACore parameters (dimensions index)) : ACore parameters outputDimension :=
  ⟨productCoefficientJet (Nat.succ_pos arity) parameters multiplication fields,
    productCoefficientJet_mem_originalCore parameters multiplication fields⟩

theorem actualMultilinearProduct_isActual {arity outputDimension : ℕ} {dimensions : Fin (arity + 1) → ℕ}
    (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin (arity + 1)) → ACore parameters (dimensions index)) :
    IsActualMultilinearProduct multiplication fields (actualMultilinearProduct parameters multiplication fields) :=
  productCoefficientJet_value (Nat.succ_pos arity) parameters multiplication fields

theorem actualMultilinearProduct_bound {arity outputDimension : ℕ} {dimensions : Fin (arity + 1) → ℕ}
    (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin (arity + 1)) → ACore parameters (dimensions index)) (grade : ℕ) :
    originalGradeNorm grade (actualMultilinearProduct parameters multiplication fields) ≤
      productGradeConstant arity grade * ‖multiplication‖ * oneHighExpression grade fields := by
  obtain ⟨majorant, nonnegative, pointBounds, normBound⟩ := product_grade_majorant_exists parameters multiplication fields grade
  apply le_trans _ normBound
  unfold originalGradeNorm
  rw [gradeCore_norm_eq_cartesianGradeSeminorm, cartesianGradeSeminorm_apply, gradeCoreCoordinates_apply]
  apply lp.norm_mono (by norm_num)
  intro cell
  rw [Real.norm_of_nonneg (nonnegative cell)]
  exact pointBounds cell

end Grad.NonlinearProduct
