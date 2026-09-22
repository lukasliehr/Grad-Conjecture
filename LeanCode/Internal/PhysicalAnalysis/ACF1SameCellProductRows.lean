import ANF9OriginalTraceCoherence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace Grad.SameCellFixedMultiplication
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

/-- Same-cell multiplication commutes with the complete original physical
weight, before differentiating. No ratio of weights from different cells occurs. -/
theorem weighted_fixed_product {input output : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    (coefficient : SmoothOperatorJet input output) (field : ClosedJet input) :
    apWeightedJet sigma gamma ell cell (apProductJet coefficient field) =
      apProductJet coefficient (apWeightedJet sigma gamma ell cell field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [apWeightedJet_value, apProductJet_value, apProductJet_value, apWeightedJet_value]
  exact (((coefficient.value point).restrictScalars ℝ).map_smul _ _).symm

def fixedIndexConstant {input output grade : ℕ} (coefficient : SmoothOperatorJet input output)
    (index : DerivativeIndex grade) : ℝ :=
  ∑ split : DerivativeSplit index, (splitMultiplicity index split : ℝ) *
    ‖smoothOperatorDerivative coefficient (derivativeMultiIndex (lowerDerivativeIndex index split))‖

theorem fixedIndexConstant_nonnegative {input output grade : ℕ}
    (coefficient : SmoothOperatorJet input output) (index : DerivativeIndex grade) : 0 ≤ fixedIndexConstant coefficient index :=
  Finset.sum_nonneg (fun split _ => mul_nonneg (Nat.cast_nonneg _)
    (norm_nonneg (smoothOperatorDerivative coefficient (derivativeMultiIndex (lowerDerivativeIndex index split)))))

theorem fixedProduct_derivative_bound {input output grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ)
    (coefficient : SmoothOperatorJet input output) (field : ClosedJet input) (index : DerivativeIndex grade) :
    scaledCellWeight L ell cell ^ (grade - derivativeOrder index) *
      ‖closedDerivativeL2 (derivativeMultiIndex index)
        (apProductJet coefficient (apWeightedJet sigma gamma ell cell field))‖ ≤
      fixedIndexConstant coefficient index * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
  apply (mul_le_mul_of_nonneg_left (apProductJet_derivativeL2_bound _ _ index)
    (pow_nonneg (scaledCellWeight_nonnegative L ell cell) _)).trans
  rw [Finset.mul_sum, fixedIndexConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro split _
  have orders := derivative_split_order index split
  have inputBound := apWeighted_word_bound L sigma gamma ell cell field (upperDerivativeIndex index split).property
    (cartesianMultiIndexWord (derivativeMultiIndex (upperDerivativeIndex index split)))
  have powers : scaledCellWeight L ell cell ^ (grade - derivativeOrder index) ≤
      scaledCellWeight L ell cell ^ (grade - derivativeOrder (upperDerivativeIndex index split)) :=
    pow_le_pow_right₀ (scaledCellWeight_one_le L ell cell) (by omega)
  have paid := (mul_le_mul_of_nonneg_right powers
    (norm_nonneg (closedDerivativeL2 (derivativeMultiIndex (upperDerivativeIndex index split))
      (apWeightedJet sigma gamma ell cell field)))).trans inputBound
  calc
    _ = ((splitMultiplicity index split : ℝ) *
        ‖smoothOperatorDerivative coefficient (derivativeMultiIndex (lowerDerivativeIndex index split))‖) *
      (scaledCellWeight L ell cell ^ (grade - derivativeOrder index) *
        ‖closedDerivativeL2 (derivativeMultiIndex (upperDerivativeIndex index split))
          (apWeightedJet sigma gamma ell cell field)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left paid (mul_nonneg (Nat.cast_nonneg _)
      (norm_nonneg (smoothOperatorDerivative coefficient (derivativeMultiIndex (lowerDerivativeIndex index split)))))

def fixedRowConstant {input output : ℕ} (grade : ℕ) (coefficient : SmoothOperatorJet input output) : ℝ :=
  Real.sqrt (Fintype.card (DerivativeIndex grade)) * ∑ index : DerivativeIndex grade, fixedIndexConstant coefficient index

theorem fixedRowConstant_nonnegative {input output : ℕ} (grade : ℕ) (coefficient : SmoothOperatorJet input output) :
    0 ≤ fixedRowConstant grade coefficient :=
  mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg (fun index _ => fixedIndexConstant_nonnegative coefficient index))

/-- Fixed-coefficient multiplication is bounded in the same original AP row,
uniformly in every physical parameter and every cell. -/
theorem fixedProduct_row_bound {input output grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ)
    (coefficient : SmoothOperatorJet input output) (field : ClosedJet input) :
    ‖apRowLinear (grade := grade) L sigma gamma ell cell (apProductJet coefficient field)‖ ≤
      fixedRowConstant grade coefficient * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
  have nonnegative : 0 ≤ ∑ index : DerivativeIndex grade, fixedIndexConstant coefficient index :=
    Finset.sum_nonneg (fun index _ => fixedIndexConstant_nonnegative coefficient index)
  have coordinate (index : DerivativeIndex grade) :
      ‖apRowLinear (grade := grade) L sigma gamma ell cell (apProductJet coefficient field) index‖ ≤
        (∑ index : DerivativeIndex grade, fixedIndexConstant coefficient index) * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
    rw [apRowLinear_apply, norm_smul, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (scaledCellWeight_nonnegative L ell cell), weighted_fixed_product]
    exact (fixedProduct_derivative_bound L sigma gamma ell cell coefficient field index).trans
      (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun other _ => fixedIndexConstant_nonnegative coefficient other) (Finset.mem_univ index)) (norm_nonneg _))
  exact (apRow_norm_bound_of_coordinates _ _ (mul_nonneg nonnegative (norm_nonneg _)) coordinate).trans_eq (mul_assoc _ _ _).symm

end Grad.SameCellFixedMultiplication
