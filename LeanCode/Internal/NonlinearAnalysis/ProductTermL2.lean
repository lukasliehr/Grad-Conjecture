import ProductAllocationIndex
import ProductOperatorL2
import ProductSeriesL2

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.NonlinearProduct

open Grad.ClosedJets Grad.CartesianState Grad.Constraints

def wordEvaluationFactor {order : ℕ} (word : CartesianWord order) : ℝ :=
  ∏ position, ‖spatialBasis (word position)‖

theorem wordEvaluationFactor_nonnegative {order : ℕ} (word : CartesianWord order) :
    0 ≤ wordEvaluationFactor word := Finset.prod_nonneg (fun _ _ => norm_nonneg _)

theorem product_point_last_sup_bound {arity : ℕ} {dimensions : Fin (arity + 1) → ℕ}
    (fields : (index : Fin (arity + 1)) → ClosedJet (dimensions index))
    (orders powers : Fin (arity + 1) → ℕ) (cells : Fin (arity + 1) → ℤ) (point : ClosedDisk) :
    (∏ index, cellFrequency (cells index) ^ powers index *
      ‖jetOperatorDerivative (orders index) (fields index) point‖) ≤
      (∏ index : Fin arity, cellFrequency (cells index.castSucc) ^ powers index.castSucc *
        ‖jetOperatorDerivative (orders index.castSucc) (fields index.castSucc)‖) *
        (cellFrequency (cells (Fin.last arity)) ^ powers (Fin.last arity) *
          ‖jetOperatorDerivative (orders (Fin.last arity)) (fields (Fin.last arity)) point‖) := by
  rw [Fin.prod_univ_castSucc]
  apply mul_le_mul_of_nonneg_right _
    (mul_nonneg (pow_nonneg (cellFrequency_pos _).le _) (norm_nonneg _))
  apply Finset.prod_le_prod
  · intro index _
    exact mul_nonneg (pow_nonneg (cellFrequency_pos _).le _) (norm_nonneg _)
  · intro index _
    exact mul_le_mul_of_nonneg_left
      (ContinuousMap.norm_coe_le_norm (jetOperatorDerivative (orders index.castSucc) (fields index.castSucc)) point)
      (pow_nonneg (cellFrequency_pos _).le _)

def productTermL2 {arity outputDimension order : ℕ} {dimensions : Fin arity → ℕ}
    (parameters : PhaseParameters) (cells : Fin arity → ℤ)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ClosedJet (dimensions index))
    (grade : ℕ) (word : CartesianWord order) : DiskL2 outputDimension :=
  cellFrequency (∑ index, cells index) ^ (grade - order) •
    closedContinuousToDiskL2 (closedDerivative
      (globalClosedJet (weightedProductSmooth parameters cells multiplication fields)
        (weightedProductSmooth_smooth parameters cells multiplication fields)) order word)

theorem productTermL2_bound {arity outputDimension order : ℕ} {dimensions : Fin (arity + 1) → ℕ}
    (parameters : PhaseParameters) (cells : Fin (arity + 1) → ℤ)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin (arity + 1)) → ClosedJet (dimensions index))
    (grade : ℕ) (word : CartesianWord order) (orderBound : order ≤ grade) :
    ‖productTermL2 parameters cells multiplication fields grade word‖ ≤
      ∑ choice : ProductAllocationIndex (arity + 1) order,
        (wordEvaluationFactor word * productAllocationConstant (arity + 1) grade order choice.1.val * ‖multiplication‖) *
        (∏ index : Fin arity,
          cellFrequency (cells index.castSucc) ^ allocationPower grade choice index.castSucc *
            ‖jetOperatorDerivative (allocationOrder choice index.castSucc)
              (phaseWeightedJet parameters (cells index.castSucc) (fields index.castSucc))‖) *
        (cellFrequency (cells (Fin.last arity)) ^ allocationPower grade choice (Fin.last arity) *
          ‖closedMapL2 (jetOperatorDerivative (allocationOrder choice (Fin.last arity))
            (phaseWeightedJet parameters (cells (Fin.last arity)) (fields (Fin.last arity))))‖) := by
  let weightedFields (index : Fin (arity + 1)) := phaseWeightedJet parameters (cells index) (fields index)
  let coefficient (choice : ProductAllocationIndex (arity + 1) order) :=
    (wordEvaluationFactor word * productAllocationConstant (arity + 1) grade order choice.1.val * ‖multiplication‖) *
      (∏ index : Fin arity, cellFrequency (cells index.castSucc) ^ allocationPower grade choice index.castSucc *
        ‖jetOperatorDerivative (allocationOrder choice index.castSucc) (weightedFields index.castSucc)‖) *
      cellFrequency (cells (Fin.last arity)) ^ allocationPower grade choice (Fin.last arity)
  have coefficientNonnegative (choice : ProductAllocationIndex (arity + 1) order) : 0 ≤ coefficient choice := by
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (wordEvaluationFactor_nonnegative word) (productAllocationConstant_nonnegative _ _ _ _))
      (norm_nonneg _)) (Finset.prod_nonneg (fun index _ =>
        mul_nonneg (pow_nonneg (cellFrequency_pos _).le _) (norm_nonneg
          (jetOperatorDerivative (allocationOrder choice index.castSucc) (weightedFields index.castSucc))))))
      (pow_nonneg (cellFrequency_pos _).le _)
  let term : C(ClosedDisk, ComplexEuclidean outputDimension) :=
    cellFrequency (∑ index, cells index) ^ (grade - order) •
      closedDerivative (globalClosedJet (weightedProductSmooth parameters cells multiplication fields)
        (weightedProductSmooth_smooth parameters cells multiplication fields)) order word
  have pointBound (point : ClosedDisk) : ‖term point‖ ≤
      ∑ choice : ProductAllocationIndex (arity + 1) order, coefficient choice *
        ‖jetOperatorDerivative (allocationOrder choice (Fin.last arity)) (weightedFields (Fin.last arity)) point‖ := by
    change ‖cellFrequency (∑ index, cells index) ^ (grade - order) •
      closedDerivative (globalClosedJet (weightedProductSmooth parameters cells multiplication fields)
        (weightedProductSmooth_smooth parameters cells multiplication fields)) order word point‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (cellFrequency_pos _).le _), globalClosedJet_derivative]
    have evaluationBound := (iteratedFDeriv ℝ order
      (weightedProductSmooth parameters cells multiplication fields) point.val).le_opNorm
        (fun position => spatialBasis (word position))
    calc
      _ ≤ cellFrequency (∑ index, cells index) ^ (grade - order) *
          (‖iteratedFDeriv ℝ order (weightedProductSmooth parameters cells multiplication fields) point.val‖ *
            wordEvaluationFactor word) := mul_le_mul_of_nonneg_left evaluationBound
              (pow_nonneg (cellFrequency_pos _).le _)
      _ = wordEvaluationFactor word * (cellFrequency (∑ index, cells index) ^ (grade - order) *
          ‖iteratedFDeriv ℝ order (weightedProductSmooth parameters cells multiplication fields) point.val‖) := by ring
      _ ≤ wordEvaluationFactor word * _ := mul_le_mul_of_nonneg_left
        (weightedProduct_finite_point_bound (Nat.succ_pos _) parameters cells multiplication fields grade order orderBound point)
        (wordEvaluationFactor_nonnegative word)
      _ ≤ _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro choice _
        calc
          _ = (wordEvaluationFactor word * productAllocationConstant (arity + 1) grade order choice.1.val * ‖multiplication‖) *
              ∏ index, cellFrequency (cells index) ^ allocationPower grade choice index *
                ‖jetOperatorDerivative (allocationOrder choice index) (weightedFields index) point‖ := by ring
          _ ≤ (wordEvaluationFactor word * productAllocationConstant (arity + 1) grade order choice.1.val * ‖multiplication‖) *
              ((∏ index : Fin arity, cellFrequency (cells index.castSucc) ^ allocationPower grade choice index.castSucc *
                ‖jetOperatorDerivative (allocationOrder choice index.castSucc) (weightedFields index.castSucc)‖) *
                (cellFrequency (cells (Fin.last arity)) ^ allocationPower grade choice (Fin.last arity) *
                  ‖jetOperatorDerivative (allocationOrder choice (Fin.last arity)) (weightedFields (Fin.last arity)) point‖)) :=
            mul_le_mul_of_nonneg_left (product_point_last_sup_bound weightedFields
              (allocationOrder choice) (allocationPower grade choice) cells point)
              (mul_nonneg (mul_nonneg (wordEvaluationFactor_nonnegative word)
                (productAllocationConstant_nonnegative _ _ _ _)) (norm_nonneg _))
          _ = _ := by dsimp only [coefficient]; ring
  have integralBound := closedMapL2_norm_le_finite_majorant term
    (fun choice : ProductAllocationIndex (arity + 1) order =>
      jetOperatorDerivative (allocationOrder choice (Fin.last arity)) (weightedFields (Fin.last arity)))
    coefficient coefficientNonnegative pointBound
  rw [closedMapL2_eq_original] at integralBound
  change ‖closedContinuousToDiskL2 (_ • _)‖ ≤ _ at integralBound
  rw [closedValueL2_real_smul] at integralBound
  apply integralBound.trans_eq
  apply Finset.sum_congr rfl
  intro choice _
  dsimp only [coefficient, weightedFields]
  ring

end Grad.NonlinearProduct
