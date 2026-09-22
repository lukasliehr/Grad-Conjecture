import ProductAllocationBounds
import ProductFiniteSeriesBound

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearProduct

open Grad.ClosedJets Grad.CartesianState

def productWordBaseConstant (arity grade : ℕ) {order : ℕ} (word : CartesianWord order) : ℝ :=
  ∑ choice : ProductAllocationIndex (arity + 1) order,
    wordEvaluationFactor word * productAllocationConstant (arity + 1) grade order choice.1.val *
      inputConvolutionConstant (allocationOrder choice)

theorem productWordBaseConstant_nonnegative (arity grade : ℕ) {order : ℕ} (word : CartesianWord order) :
    0 ≤ productWordBaseConstant arity grade word := Finset.sum_nonneg (fun _ _ => mul_nonneg
      (mul_nonneg (wordEvaluationFactor_nonnegative word) (productAllocationConstant_nonnegative _ _ _ _))
      (inputConvolutionConstant_nonnegative _))

def productWordConstant (arity grade : ℕ) {order : ℕ} (word : CartesianWord order) : ℝ :=
  productWordBaseConstant arity grade word * allocationInterpolationConstant grade ^ (arity + 1)

theorem productWordConstant_nonnegative (arity grade : ℕ) {order : ℕ} (word : CartesianWord order) :
    0 ≤ productWordConstant arity grade word :=
  mul_nonneg (Finset.sum_nonneg (fun _ _ => mul_nonneg
    (mul_nonneg (wordEvaluationFactor_nonnegative word) (productAllocationConstant_nonnegative _ _ _ _))
    (inputConvolutionConstant_nonnegative _)))
    (pow_nonneg (zero_le_one.trans (allocationInterpolationConstant_one_le _)) _)

theorem product_word_majorant_of_allocated_bound {arity outputDimension order : ℕ} {dimensions : Fin (arity + 1) → ℕ}
    (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin (arity + 1)) → ACore parameters (dimensions index))
    (grade : ℕ) (word : CartesianWord order) (orderBound : order ≤ grade)
    (allocationBound : ℝ)
    (bounded : ∀ orders : Fin (arity + 1) → ℕ, (∑ index, orders index) = grade →
      allocatedNormProduct orders fields ≤ allocationBound) :
    ∃ majorant : lp (fun _ : ℤ => ℝ) 2,
      (∀ cell, 0 ≤ majorant cell) ∧
      (∀ cell, ‖cellFrequency cell ^ (grade - order) • closedContinuousToDiskL2
        (closedDerivative (weightedProductCoefficientJet (Nat.succ_pos arity) parameters multiplication fields cell)
          order word)‖ ≤ majorant cell) ∧
      ‖majorant‖ ≤ productWordBaseConstant arity grade word * ‖multiplication‖ * allocationBound := by
  classical
  choose outputs outputSums outputNonnegative outputBounds using
    (fun choice : ProductAllocationIndex (arity + 1) order => allocated_convolution_exists_sharp parameters fields
      (allocationOrder choice) (allocationPower grade choice))
  let coefficients (choice : ProductAllocationIndex (arity + 1) order) : ℝ :=
    wordEvaluationFactor word * productAllocationConstant (arity + 1) grade order choice.1.val * ‖multiplication‖
  have coefficientNonnegative (choice : ProductAllocationIndex (arity + 1) order) : 0 ≤ coefficients choice :=
    mul_nonneg (mul_nonneg (wordEvaluationFactor_nonnegative word)
      (productAllocationConstant_nonnegative _ _ _ _)) (norm_nonneg _)
  let majorant : lp (fun _ : ℤ => ℝ) 2 := ∑ choice, coefficients choice • outputs choice
  have majorantValue (cell : ℤ) : majorant cell = ∑ choice, coefficients choice * outputs choice cell := by
    simp only [majorant, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  refine ⟨majorant, ?_, ?_, ?_⟩
  · intro cell
    rw [majorantValue]
    exact Finset.sum_nonneg (fun choice _ => mul_nonneg (coefficientNonnegative choice) (outputNonnegative choice cell))
  · intro cell
    rw [majorantValue]
    let kernel (assignment : CellAssignments (arity + 1) cell) := productTermL2 parameters assignment.val multiplication
      (fun index => (fields index).val (assignment.val index)) grade word
    have kernelSum : HasSum kernel
        (cellFrequency cell ^ (grade - order) • closedContinuousToDiskL2
          (closedDerivative (weightedProductCoefficientJet (Nat.succ_pos arity) parameters multiplication fields cell)
            order word)) := by
      have scaled := (weightedProductCoefficientJet_L2_hasSum (Nat.succ_pos arity) parameters multiplication fields cell word).const_smul
        (cellFrequency cell ^ (grade - order))
      have functionsEqual : (fun assignment : CellAssignments (arity + 1) cell =>
          cellFrequency cell ^ (grade - order) • closedContinuousToDiskL2
            (closedDerivative (Grad.Constraints.globalClosedJet
              (weightedProductSmooth parameters assignment.val multiplication
                (fun index => (fields index).val (assignment.val index)))
              (weightedProductSmooth_smooth parameters assignment.val multiplication _)) order word)) = kernel := by
        funext assignment
        dsimp only [kernel, productTermL2]
        rw [assignment.property]
      rw [functionsEqual] at scaled
      exact scaled
    apply norm_hasSum_le_finite_majorants kernel _ kernelSum _
      (fun choice => outputs choice cell) coefficients (fun choice => outputSums choice cell)
    intro assignment
    have termBound := productTermL2_bound parameters assignment.val multiplication
      (fun index => (fields index).val (assignment.val index)) grade word orderBound
    simpa only [kernel, coefficients, inputSupSequence, weightedOperatorL2Sequence_value, mul_assoc] using termBound
  · calc
      _ ≤ ∑ choice, ‖coefficients choice • outputs choice‖ := norm_sum_le _ _
      _ = ∑ choice, coefficients choice * ‖outputs choice‖ := by
        apply Finset.sum_congr rfl
        intro choice _
        rw [norm_smul, Real.norm_of_nonneg (coefficientNonnegative choice)]
      _ ≤ ∑ choice, coefficients choice *
          (inputConvolutionConstant (allocationOrder choice) * allocationBound) := by
        apply Finset.sum_le_sum
        intro choice _
        apply mul_le_mul_of_nonneg_left _ (coefficientNonnegative choice)
        exact (outputBounds choice).trans (mul_le_mul_of_nonneg_left
          (bounded
            (fun index => allocationOrder choice index + allocationPower grade choice index)
            (allocationOrderPower_total grade choice orderBound))
          (inputConvolutionConstant_nonnegative _))
      _ = _ := by
        unfold productWordBaseConstant
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro choice _
        dsimp only [coefficients]
        ring

theorem product_word_majorant_exists {arity outputDimension order : ℕ} {dimensions : Fin (arity + 1) → ℕ}
    (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin (arity + 1)) → ACore parameters (dimensions index))
    (grade : ℕ) (word : CartesianWord order) (orderBound : order ≤ grade) :
    ∃ majorant : lp (fun _ : ℤ => ℝ) 2,
      (∀ cell, 0 ≤ majorant cell) ∧
      (∀ cell, ‖cellFrequency cell ^ (grade - order) • closedContinuousToDiskL2
        (closedDerivative (weightedProductCoefficientJet (Nat.succ_pos arity) parameters multiplication fields cell)
          order word)‖ ≤ majorant cell) ∧
      ‖majorant‖ ≤ productWordConstant arity grade word * ‖multiplication‖ * oneHighExpression grade fields := by
  obtain ⟨majorant, nonnegative, pointBound, normBound⟩ := product_word_majorant_of_allocated_bound
    parameters multiplication fields grade word orderBound
    (allocationInterpolationConstant grade ^ (arity + 1) * oneHighExpression grade fields)
    (fun orders total => (allocatedNormProduct_le_all_shifted orders fields).trans
      (original_allocated_product_all_grades (Nat.succ_pos arity) grade orders total fields))
  refine ⟨majorant, nonnegative, pointBound, normBound.trans_eq ?_⟩
  unfold productWordConstant
  ring

end Grad.NonlinearProduct
