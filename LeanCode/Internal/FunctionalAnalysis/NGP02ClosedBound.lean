import NGP02Collar

noncomputable section

set_option maxHeartbeats 800000

open Set
open scoped BigOperators

namespace Grad.CartesianState

open Grad.ClosedJets
open Grad.DiskExtension.Operator

local instance ngp02ClosedBoundCellPeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨by positivity⟩

@[simp] theorem closedPhysicalOperatorDerivative_basis
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (point : DiskCellDomain) (word : MixedCartesianWord order) :
    closedPhysicalOperatorDerivative field order point
        (fun position => spatialCellBasis (word position)) =
      closedMixedDerivative field order word point := by
  classical
  change (∑ coefficientWord : MixedCartesianWord order,
      (spatialCellWordCoefficient coefficientWord).smulRight
        (closedMixedDerivative field order coefficientWord point))
        (fun position => spatialCellBasis (word position)) = _
  rw [sum_apply]
  rw [Finset.sum_eq_single word]
  · rw [ContinuousMultilinearMap.smulRight_apply,
      spatialCellWordCoefficient_basis, if_pos rfl, one_smul]
  · intro other _ otherNe
    rw [ContinuousMultilinearMap.smulRight_apply,
      spatialCellWordCoefficient_basis, if_neg otherNe, zero_smul]
  · simp

theorem closedPhysicalCNorm_nonnegative {dimension j : ℕ}
    (field : DiskCellClosedJet dimension) :
    0 ≤ closedPhysicalCNorm field j := by
  exact (norm_nonneg (closedPhysicalOperatorDerivative field 0)).trans
    (closedPhysicalOperatorDerivative_norm_le_cNorm field (Nat.zero_le j))

/-- Every coordinate derivative is bounded by the genuine Euclidean
operator `C^j` norm, with no change of domain or derivative order. -/
theorem closedMixedDerivative_norm_le_physicalCNorm
    {dimension order j : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (orderLe : order ≤ j) :
    ‖closedMixedDerivative field order word‖ ≤
      closedPhysicalCNorm field j := by
  rw [ContinuousMap.norm_le _ (closedPhysicalCNorm_nonnegative field)]
  intro point
  calc
    ‖closedMixedDerivative field order word point‖ =
        ‖closedPhysicalOperatorDerivative field order point
          (fun position => spatialCellBasis (word position))‖ := by
      rw [closedPhysicalOperatorDerivative_basis]
    _ ≤ ‖closedPhysicalOperatorDerivative field order point‖ *
        ∏ position, ‖spatialCellBasis (word position)‖ :=
      (closedPhysicalOperatorDerivative field order point).le_opNorm _
    _ = ‖closedPhysicalOperatorDerivative field order point‖ := by
      simp only [spatialCellBasis_norm, Finset.prod_const_one, mul_one]
    _ ≤ ‖closedPhysicalOperatorDerivative field order‖ :=
      (closedPhysicalOperatorDerivative field order).norm_coe_le_norm point
    _ ≤ closedPhysicalCNorm field j :=
      closedPhysicalOperatorDerivative_norm_le_cNorm field orderLe

/-- Finite coordinate-comparison factor used by P09's exterior quadratic
majorant.  It depends only on the derivative grade. -/
noncomputable def closedCNormQuadraticFactor (grade : ℕ) : ℝ :=
  ∑ order ∈ Finset.range (grade + 1),
    closedWordCoefficientSum order *
      ∑ word : MixedCartesianWord order,
        ‖spatialCellWordCoefficient word‖

theorem closedCNormQuadraticFactor_nonnegative (grade : ℕ) :
    0 ≤ closedCNormQuadraticFactor grade := by
  unfold closedCNormQuadraticFactor
  apply Finset.sum_nonneg
  intro order _
  exact mul_nonneg (closedWordCoefficientSum_nonnegative order)
    (Finset.sum_nonneg fun word _ => norm_nonneg _)

/-- P09's finite quadratic source is controlled by the literal closed
physical `C^grade` norm. -/
theorem closedDerivativeGradeQuadraticGlobalBound_le_physicalCNorm
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (grade : ℕ) :
    closedDerivativeGradeQuadraticGlobalBound field grade ≤
      closedCNormQuadraticFactor grade * closedPhysicalCNorm field grade ^ 2 := by
  unfold closedDerivativeGradeQuadraticGlobalBound
    closedCNormQuadraticFactor
  calc
    (∑ order ∈ Finset.range (grade + 1),
        closedWordCoefficientSum order *
          ∑ word : MixedCartesianWord order,
            ‖spatialCellWordCoefficient word‖ *
              ‖closedMixedDerivative field order word‖ ^ 2) ≤
      ∑ order ∈ Finset.range (grade + 1),
        closedWordCoefficientSum order *
          ∑ word : MixedCartesianWord order,
            ‖spatialCellWordCoefficient word‖ *
              closedPhysicalCNorm field grade ^ 2 := by
        apply Finset.sum_le_sum
        intro order orderMembership
        apply mul_le_mul_of_nonneg_left _
          (closedWordCoefficientSum_nonnegative order)
        apply Finset.sum_le_sum
        intro word _
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact pow_le_pow_left₀ (norm_nonneg _)
          (closedMixedDerivative_norm_le_physicalCNorm field word
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp orderMembership))) 2
    _ = (∑ order ∈ Finset.range (grade + 1),
        closedWordCoefficientSum order *
          ∑ word : MixedCartesianWord order,
            ‖spatialCellWordCoefficient word‖) *
          closedPhysicalCNorm field grade ^ 2 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro order _
      rw [← Finset.sum_mul]
      ring

end Grad.CartesianState
