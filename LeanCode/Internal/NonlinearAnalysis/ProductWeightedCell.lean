import ProductWeightedInputs
import ProductPhaseDerivative

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.NonlinearProduct

open Grad.ClosedJets Grad.CartesianState Grad.Constraints

theorem productDefect_weight_balance {arity : ℕ} (parameters : PhaseParameters)
    (cells : Fin arity → ℤ) (point : SpatialPlane) :
    productDefectMultiplier parameters cells point *
      (∏ index, cartesianWeight parameters (cells index) point) =
      cartesianWeight parameters (∑ index, cells index) point := by
  simp only [productDefectMultiplier, productPhaseDefect, cartesianWeight_exp]
  rw [← Real.exp_sum, ← Real.exp_add]
  congr 1
  ring

def weightedProductSmooth {arity outputDimension : ℕ} {dimensions : Fin arity → ℕ}
    (parameters : PhaseParameters) (cells : Fin arity → ℤ)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ClosedJet (dimensions index))
    (point : SpatialPlane) : ComplexEuclidean outputDimension :=
  productDefectMultiplier parameters cells point • jetMultilinearSmoothField multiplication
    (fun index => phaseWeightedJet parameters (cells index) (fields index)) point

theorem weightedProductSmooth_smooth {arity outputDimension : ℕ} {dimensions : Fin arity → ℕ}
    (parameters : PhaseParameters) (cells : Fin arity → ℤ)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ClosedJet (dimensions index)) :
    ContDiff ℝ ∞ (weightedProductSmooth parameters cells multiplication fields) :=
  (productDefectMultiplier_smooth parameters cells).smul
    (jetMultilinearSmoothField_smooth multiplication _)

/-- Exact phase bookkeeping on actual closed jets, including every boundary
derivative by jet extensionality. -/
theorem phaseWeighted_multilinearProduct {arity outputDimension : ℕ}
    {dimensions : Fin arity → ℕ} (parameters : PhaseParameters) (cells : Fin arity → ℤ)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ClosedJet (dimensions index)) :
    phaseWeightedJet parameters (∑ index, cells index) (jetMultilinearProduct multiplication fields) =
      globalClosedJet (weightedProductSmooth parameters cells multiplication fields)
        (weightedProductSmooth_smooth parameters cells multiplication fields) := by
  symm
  apply globalClosedJet_eq_of_restriction
  intro point
  simp only [weightedProductSmooth, jetMultilinearSmoothField, smoothClosedExtension_value,
    phaseWeightedJet_value, jetMultilinearProduct_value]
  change productDefectMultiplier parameters cells point.val •
    (multiplication.restrictScalars ℝ).toMultilinearMap (fun index =>
      cartesianWeight parameters (cells index) point.val • (fields index).value point) = _
  rw [(multiplication.restrictScalars ℝ).toMultilinearMap.map_smul_univ]
  rw [smul_smul, productDefect_weight_balance]
  rfl

theorem weightedProductSmooth_derivative_bound {arity outputDimension : ℕ}
    {dimensions : Fin arity → ℕ} (positiveArity : 0 < arity)
    (parameters : PhaseParameters) (cells : Fin arity → ℤ)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ClosedJet (dimensions index)) (order : ℕ) (point : ClosedDisk) :
    ‖iteratedFDeriv ℝ order (weightedProductSmooth parameters cells multiplication fields) point.val‖ ≤
      ∑ defectOrder ∈ Finset.range (order + 1), (order.choose defectOrder : ℝ) *
        (productDefectDerivativeConstant arity defectOrder * productFrequency cells ^ defectOrder) *
        (‖multiplication‖ * derivativeAllocation arity
          (fun index rank => ‖jetOperatorDerivative rank
            (phaseWeightedJet parameters (cells index) (fields index)) point‖) (order - defectOrder)) := by
  apply (norm_iteratedFDeriv_smul_le (productDefectMultiplier_smooth parameters cells)
    (jetMultilinearSmoothField_smooth multiplication _)
    point.val (by exact_mod_cast le_top)).trans
  apply Finset.sum_le_sum
  intro defectOrder _
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left
      (productDefectMultiplier_iterated_bound positiveArity parameters cells defectOrder point)
      (Nat.cast_nonneg _)
  · have allocationBound := multilinear_iterated_derivative_allocation arity (multiplication.restrictScalars ℝ)
        (fun index => smoothClosedExtension (phaseWeightedJet parameters (cells index) (fields index)))
        (fun index => smoothClosedExtension_smooth _) (order - defectOrder) point.val
    rw [ContinuousMultilinearMap.norm_restrictScalars] at allocationBound
    exact allocationBound
  · exact norm_nonneg _
  · exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (productDefectDerivativeConstant_nonnegative _ _)
        (pow_nonneg (productFrequency_nonnegative cells) _))

end Grad.NonlinearProduct
