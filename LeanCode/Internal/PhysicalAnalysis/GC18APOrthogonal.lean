import GC18APClosure
import AngularGradeBound

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.AnalyticWeights.Calculus Grad.GaugeCoefficients.Radial

theorem apWeight_orthogonal (sigma gamma ell : ℝ) (cell : ℤ)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (point : SpatialPlane) :
    originalWeight sigma gamma ell cell (orthogonal point) = originalWeight sigma gamma ell cell point := by
  unfold originalWeight physicalWeight
  rw [orthogonal.norm_map]

theorem apWeightedJet_orthogonal {dimension : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ClosedJet dimension) :
    orthogonalJet orthogonal (apWeightedJet sigma gamma ell cell field) =
      apWeightedJet sigma gamma ell cell (orthogonalJet orthogonal field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change (apWeightedJet sigma gamma ell cell field).value (orthogonalClosedPoint orthogonal point) = _
  rw [apWeightedJet_value, apWeightedJet_value]
  change originalWeight sigma gamma ell cell (orthogonal point.val) • field.value (orthogonalClosedPoint orthogonal point) = _
  rw [apWeight_orthogonal]
  rfl

theorem apWeighted_word_bound {dimension grade order : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ)
    (field : ClosedJet dimension) (orderBound : order ≤ grade) (word : CartesianWord order) :
    scaledCellWeight L ell cell ^ (grade - order) *
      ‖closedContinuousToDiskL2 (closedDerivative (apWeightedJet sigma gamma ell cell field) order word)‖ ≤
      ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
  have bound := PiLp.norm_apply_le (apRowLinear (grade := grade) L sigma gamma ell cell field)
    (wordGradeIndex orderBound word)
  rw [apRowLinear_apply, norm_smul, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (scaledCellWeight_nonnegative L ell cell)] at bound
  change scaledCellWeight L ell cell ^ (grade - cartesianOrder (wordGradeIndex orderBound word).toCartesian) *
    ‖closedContinuousToDiskL2 (closedMultiDerivative (apWeightedJet sigma gamma ell cell field)
      (wordGradeIndex orderBound word).toCartesian)‖ ≤ _ at bound
  rw [wordGradeIndex_order, wordGradeIndex_cartesian, ← closedDerivative_eq_multi] at bound
  exact bound

theorem apWeighted_orthogonal_word_bound {dimension grade order : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ClosedJet dimension)
    (orderBound : order ≤ grade) (word : CartesianWord order) :
    scaledCellWeight L ell cell ^ (grade - order) *
      ‖closedContinuousToDiskL2 (closedDerivative (apWeightedJet sigma gamma ell cell (orthogonalJet orthogonal field)) order word)‖ ≤
      (2 : ℝ) ^ grade * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
  rw [← apWeightedJet_orthogonal]
  calc
    _ ≤ scaledCellWeight L ell cell ^ (grade - order) *
        ∑ target : CartesianWord order, ‖closedContinuousToDiskL2
          (closedDerivative (apWeightedJet sigma gamma ell cell field) order target)‖ :=
      mul_le_mul_of_nonneg_left (orthogonal_derivative_L2_norm_le orthogonal _ word)
        (pow_nonneg (scaledCellWeight_nonnegative L ell cell) _)
    _ = ∑ target : CartesianWord order, scaledCellWeight L ell cell ^ (grade - order) *
        ‖closedContinuousToDiskL2 (closedDerivative (apWeightedJet sigma gamma ell cell field) order target)‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ _target : CartesianWord order, ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ :=
      Finset.sum_le_sum (fun target _ => apWeighted_word_bound L sigma gamma ell cell field orderBound target)
    _ = (2 : ℝ) ^ order * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) orderBound) (norm_nonneg _)

theorem apOrthogonal_coordinate_bound {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ClosedJet dimension) (index : DerivativeIndex grade) :
    ‖apRowLinear L sigma gamma ell cell (orthogonalJet orthogonal field) index‖ ≤
      (2 : ℝ) ^ grade * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
  rw [apRowLinear_apply, norm_smul, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (scaledCellWeight_nonnegative L ell cell)]
  exact apWeighted_orthogonal_word_bound L sigma gamma ell cell orthogonal field index.property
    (cartesianMultiIndexWord (derivativeMultiIndex index))

theorem apRow_norm_bound_of_coordinates {dimension grade : ℕ} (row : APRow dimension grade) (bound : ℝ)
    (nonnegative : 0 ≤ bound) (bounded : ∀ index, ‖row index‖ ≤ bound) :
    ‖row‖ ≤ Real.sqrt (Fintype.card (DerivativeIndex grade)) * bound := by
  have square : ‖row‖ ^ 2 ≤ (Fintype.card (DerivativeIndex grade) : ℝ) * bound ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _index : DerivativeIndex grade, bound ^ 2 := Finset.sum_le_sum (fun index _ =>
        pow_le_pow_left₀ (norm_nonneg _) (bounded index) 2)
      _ = _ := by simp
  have rootSquare := Real.sq_sqrt (show (0 : ℝ) ≤ Fintype.card (DerivativeIndex grade) by positivity)
  have rootNonnegative := Real.sqrt_nonneg (Fintype.card (DerivativeIndex grade) : ℝ)
  have rowNonnegative := norm_nonneg row
  have productNonnegative := mul_nonneg rootNonnegative nonnegative
  nlinarith [sq_nonneg (‖row‖ - Real.sqrt (Fintype.card (DerivativeIndex grade)) * bound)]

theorem apOrthogonal_row_bound {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ClosedJet dimension) :
    ‖apRowLinear (grade := grade) L sigma gamma ell cell (orthogonalJet orthogonal field)‖ ≤
      orthogonalGradeConstant grade * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
  have bound := apRow_norm_bound_of_coordinates _ ((2 : ℝ) ^ grade * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖)
    (by positivity) (apOrthogonal_coordinate_bound L sigma gamma ell cell orthogonal field)
  exact bound.trans_eq (by unfold orthogonalGradeConstant; ring)

end Grad.GaugeCoefficients.Physical.RadialLedger
