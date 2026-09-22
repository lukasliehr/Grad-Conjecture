import ProductTermL2
import ProductFiberConvolution

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearProduct

open Grad.ClosedJets Grad.CartesianState

def inputSupSequence {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (order power : ℕ) (cell : ℤ) : ℝ :=
  cellFrequency cell ^ power * ‖jetOperatorDerivative order (phaseWeightedJet parameters cell (field.val cell))‖

theorem inputSupSequence_nonnegative {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (order power : ℕ) (cell : ℤ) :
    0 ≤ inputSupSequence parameters field order power cell :=
  mul_nonneg (pow_nonneg (cellFrequency_pos cell).le power)
    (norm_nonneg (jetOperatorDerivative order (phaseWeightedJet parameters cell (field.val cell))))

def inputConvolutionConstant {arity : ℕ} (orders : Fin (arity + 1) → ℕ) : ℝ :=
  (∏ index : Fin arity, wordOperatorFactor (orders index.castSucc) * m15EvaluationConstant) *
    wordOperatorFactor (orders (Fin.last arity))

theorem inputConvolutionConstant_nonnegative {arity : ℕ} (orders : Fin (arity + 1) → ℕ) :
    0 ≤ inputConvolutionConstant orders := by
  apply mul_nonneg _ (wordOperatorFactor_nonnegative _)
  apply Finset.prod_nonneg
  intro index _
  exact mul_nonneg (wordOperatorFactor_nonnegative _) m15EvaluationConstant_nonneg

theorem allocated_convolution_exists_sharp {arity : ℕ} {dimensions : Fin (arity + 1) → ℕ}
    (parameters : PhaseParameters)
    (fields : (index : Fin (arity + 1)) → ACore parameters (dimensions index))
    (orders powers : Fin (arity + 1) → ℕ) :
    ∃ output : lp (fun _ : ℤ => ℝ) 2,
      (∀ cell, HasSum (fun assignment : CellAssignments (arity + 1) cell =>
        (∏ index : Fin arity, inputSupSequence parameters (fields index.castSucc)
          (orders index.castSucc) (powers index.castSucc) (assignment.val index.castSucc)) *
          weightedOperatorL2Sequence parameters (fields (Fin.last arity))
            (orders (Fin.last arity)) (powers (Fin.last arity)) (assignment.val (Fin.last arity))) (output cell)) ∧
      (∀ cell, 0 ≤ output cell) ∧
      ‖output‖ ≤ inputConvolutionConstant orders *
        ((∏ index : Fin arity, originalGradeNorm
          (orders index.castSucc + powers index.castSucc + 3) (fields index.castSucc)) *
          originalGradeNorm (orders (Fin.last arity) + powers (Fin.last arity)) (fields (Fin.last arity))) := by
  obtain ⟨output, sums, nonnegative, bound⟩ := fiber_convolution_exists
    (fun index : Fin arity => inputSupSequence parameters (fields index.castSucc)
      (orders index.castSucc) (powers index.castSucc))
    (fun index => inputSupSequence_nonnegative parameters _ _ _)
    (fun index => weighted_operator_sup_summable parameters _ _ _)
    (weightedOperatorL2Sequence parameters (fields (Fin.last arity))
      (orders (Fin.last arity)) (powers (Fin.last arity)))
    (weightedOperatorL2Sequence_nonnegative parameters _ _ _)
  refine ⟨output, sums, nonnegative, bound.trans ?_⟩
  have lastBound : ‖weightedOperatorL2Sequence parameters (fields (Fin.last arity))
      (orders (Fin.last arity)) (powers (Fin.last arity))‖ ≤
      wordOperatorFactor (orders (Fin.last arity)) *
        originalGradeNorm (orders (Fin.last arity) + powers (Fin.last arity)) (fields (Fin.last arity)) :=
    weightedOperatorL2Sequence_norm_bound parameters _ _ _
  calc
    _ ≤ (∏ index : Fin arity, (wordOperatorFactor (orders index.castSucc) * m15EvaluationConstant) *
          originalGradeNorm (orders index.castSucc + powers index.castSucc + 3) (fields index.castSucc)) *
        (wordOperatorFactor (orders (Fin.last arity)) *
          originalGradeNorm (orders (Fin.last arity) + powers (Fin.last arity)) (fields (Fin.last arity))) := by
      exact mul_le_mul (Finset.prod_le_prod
          (fun index _ => tsum_nonneg (inputSupSequence_nonnegative parameters _ _ _))
          (fun index _ => weighted_operator_sup_tsum_bound parameters _ _ _)) lastBound (norm_nonneg _)
        (Finset.prod_nonneg (fun index _ => mul_nonneg
          (mul_nonneg (wordOperatorFactor_nonnegative _) m15EvaluationConstant_nonneg)
          (originalGradeNorm_nonnegative _ _)))
    _ = _ := by rw [Finset.prod_mul_distrib]; unfold inputConvolutionConstant; ring

end Grad.NonlinearProduct
