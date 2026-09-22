import ProductSeriesMajorant
import ProductClosedSeries

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.NonlinearProduct

open Grad.ClosedJets Grad.CartesianState

def seriesProductConstant (arity order : ℕ) : ℝ :=
  ∑ defect ∈ Finset.range (order + 1), (order.choose defect : ℝ) *
    productDefectDerivativeConstant arity defect * (arity : ℝ) ^ order *
      allocationMultiplicity arity (order - defect)

theorem seriesProductConstant_nonnegative (arity order : ℕ) :
    0 ≤ seriesProductConstant arity order :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (productDefectDerivativeConstant_nonnegative _ _))
      (pow_nonneg (Nat.cast_nonneg _) _)) (allocationMultiplicity_nonnegative _ _))

theorem weightedProduct_series_point_bound {arity outputDimension : ℕ}
    {dimensions : Fin arity → ℕ} (positiveArity : 0 < arity)
    (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ACore parameters (dimensions index))
    (cells : Fin arity → ℤ) (order : ℕ) (point : ClosedDisk) :
    ‖iteratedFDeriv ℝ order (weightedProductSmooth parameters cells multiplication
      (fun index => (fields index).val (cells index))) point.val‖ ≤
      seriesProductConstant arity order * ‖multiplication‖ *
        ∏ index, seriesInputMajorant parameters (fields index) order (cells index) := by
  apply (weightedProductSmooth_derivative_bound positiveArity parameters cells multiplication _ order point).trans
  calc
    _ ≤ ∑ defect ∈ Finset.range (order + 1),
        ((order.choose defect : ℝ) * productDefectDerivativeConstant arity defect *
          (arity : ℝ) ^ order * allocationMultiplicity arity (order - defect)) *
            ‖multiplication‖ * ∏ index, seriesInputMajorant parameters (fields index) order (cells index) := by
      apply Finset.sum_le_sum
      intro defect defectIn
      have defectBound : defect ≤ order := Nat.le_of_lt_succ (Finset.mem_range.mp defectIn)
      let allocation := derivativeAllocation arity
        (fun index rank => ‖jetOperatorDerivative rank
          (phaseWeightedJet parameters (cells index) ((fields index).val (cells index))) point‖)
        (order - defect)
      have allocationNonnegative : 0 ≤ allocation := derivativeAllocation_nonnegative _ (fun _ _ => norm_nonneg _) _
      have coefficientNonnegative : 0 ≤ (order.choose defect : ℝ) * productDefectDerivativeConstant arity defect :=
        mul_nonneg (Nat.cast_nonneg _) (productDefectDerivativeConstant_nonnegative _ _)
      change (order.choose defect : ℝ) *
        (productDefectDerivativeConstant arity defect * productFrequency cells ^ defect) *
        (‖multiplication‖ * allocation) ≤ _
      calc
        _ = ((order.choose defect : ℝ) * productDefectDerivativeConstant arity defect) *
            productFrequency cells ^ defect * (‖multiplication‖ * allocation) := by ring
        _ ≤ ((order.choose defect : ℝ) * productDefectDerivativeConstant arity defect) *
            ((arity : ℝ) ^ order * ∏ index, cellFrequency (cells index) ^ order) *
              (‖multiplication‖ * allocation) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (productFrequency_power_le_product positiveArity cells order defect defectBound) coefficientNonnegative)
            (mul_nonneg (norm_nonneg multiplication) allocationNonnegative)
        _ = ((order.choose defect : ℝ) * productDefectDerivativeConstant arity defect *
            (arity : ℝ) ^ order * ‖multiplication‖) *
              ((∏ index, cellFrequency (cells index) ^ order) * allocation) := by ring
        _ ≤ ((order.choose defect : ℝ) * productDefectDerivativeConstant arity defect *
            (arity : ℝ) ^ order * ‖multiplication‖) *
              (allocationMultiplicity arity (order - defect) *
                ∏ index, seriesInputMajorant parameters (fields index) order (cells index)) :=
          mul_le_mul_of_nonneg_left
            (derivativeAllocation_series_bound parameters fields cells order (order - defect) (Nat.sub_le _ _) point)
            (mul_nonneg (mul_nonneg coefficientNonnegative (pow_nonneg (Nat.cast_nonneg _) order))
              (norm_nonneg multiplication))
        _ = _ := by ring
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; rfl

def productSeriesMajorant {arity outputDimension : ℕ} {dimensions : Fin arity → ℕ}
    (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ACore parameters (dimensions index))
    (order : ℕ) (cells : Fin arity → ℤ) : ℝ :=
  seriesProductConstant arity order * ‖multiplication‖ *
    ∏ index, seriesInputMajorant parameters (fields index) order (cells index)

theorem productSeriesMajorant_summable {arity outputDimension : ℕ} {dimensions : Fin arity → ℕ}
    (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin arity) → ACore parameters (dimensions index)) (order : ℕ) :
    Summable (productSeriesMajorant parameters multiplication fields order) :=
  (finite_tensor_hasSum arity (fun index => seriesInputMajorant parameters (fields index) order)
    (fun index => seriesInputMajorant_nonnegative parameters (fields index) order)
    (fun index => seriesInputMajorant_summable parameters (fields index) order)).summable.mul_left
      (seriesProductConstant arity order * ‖multiplication‖)

end Grad.NonlinearProduct
