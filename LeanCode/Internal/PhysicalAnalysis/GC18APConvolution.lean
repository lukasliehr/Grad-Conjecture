import GC18APRowAction
import GC10Convolution

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

theorem apSingleOperator_norm_summable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ} (allocation : APAllocation grade)
    (coefficient : WeightedAmbient grade inputDimension outputDimension) :
    Summable (fun shift : ℤ => ‖apSingleOperator admissible allocation shift (coefficient (shift, apCoefficientIndex allocation))‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun shift => apSingleOperator_bound admissible allocation shift _)
    ((coordinate_norm_summable coefficient (apCoefficientIndex allocation)).mul_left (apAllocationConstant L sigma gamma allocation))

/-- The all-cell convolution for one triple-Leibniz allocation. -/
def apAllocatedOperator {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ} (allocation : APAllocation grade)
    (coefficient : WeightedAmbient grade inputDimension outputDimension) :
    APAmbient inputDimension grade →L[ℂ] APAmbient outputDimension grade :=
  ∑' shift : ℤ, apSingleOperator admissible allocation shift (coefficient (shift, apCoefficientIndex allocation))

theorem apAllocatedOperator_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ} (allocation : APAllocation grade)
    (coefficient : WeightedAmbient grade inputDimension outputDimension) :
    ‖apAllocatedOperator admissible allocation coefficient‖ ≤ apAllocationConstant L sigma gamma allocation * ‖coefficient‖ := by
  have summable := apSingleOperator_norm_summable admissible allocation coefficient
  apply (norm_tsum_le_tsum_norm summable).trans
  calc
    _ ≤ ∑' shift : ℤ, apAllocationConstant L sigma gamma allocation * ‖coefficient (shift, apCoefficientIndex allocation)‖ :=
      summable.tsum_le_tsum (fun shift => apSingleOperator_bound admissible allocation shift _)
        ((coordinate_norm_summable coefficient (apCoefficientIndex allocation)).mul_left _)
    _ = apAllocationConstant L sigma gamma allocation * ∑' shift : ℤ, ‖coefficient (shift, apCoefficientIndex allocation)‖ := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (coordinate_norm_sum_le coefficient (apCoefficientIndex allocation))
      (apAllocationConstant_nonnegative admissible allocation)

/-- The exact weighted derivative-array action. Membership in the original
AP2 closure and literal product realization are proved at the core boundary. -/
def apAmbientMultiplier {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ}
    (coefficient : WeightedAmbient grade inputDimension outputDimension) :
    APAmbient inputDimension grade →L[ℂ] APAmbient outputDimension grade :=
  ∑ allocation : APAllocation grade, (apMultiplicity allocation : ℂ) • apAllocatedOperator admissible allocation coefficient

theorem apAmbientMultiplier_norm_le {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ}
    (coefficient : WeightedAmbient grade inputDimension outputDimension) :
    ‖apAmbientMultiplier admissible coefficient‖ ≤ apMultiplierConstant L sigma gamma grade * ‖coefficient‖ := by
  apply (norm_sum_le _ _).trans
  calc
    _ = ∑ allocation : APAllocation grade, (apMultiplicity allocation : ℝ) *
        ‖apAllocatedOperator admissible allocation coefficient‖ := by
      apply Finset.sum_congr rfl
      intro allocation _
      rw [norm_smul, Complex.norm_natCast]
    _ ≤ ∑ allocation : APAllocation grade, (apMultiplicity allocation : ℝ) *
        (apAllocationConstant L sigma gamma allocation * ‖coefficient‖) :=
      Finset.sum_le_sum (fun allocation _ => mul_le_mul_of_nonneg_left
        (apAllocatedOperator_bound admissible allocation coefficient) (Nat.cast_nonneg _))
    _ = _ := by unfold apMultiplierConstant; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring

theorem apAmbientMultiplier_apply_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ}
    (coefficient : WeightedAmbient grade inputDimension outputDimension) (field : APAmbient inputDimension grade) :
    ‖apAmbientMultiplier admissible coefficient field‖ ≤
      apMultiplierConstant L sigma gamma grade * ‖coefficient‖ * ‖field‖ :=
  ((apAmbientMultiplier admissible coefficient).le_opNorm field).trans
    (mul_le_mul_of_nonneg_right (apAmbientMultiplier_norm_le admissible coefficient) (norm_nonneg _))

end Grad.GaugeCoefficients.Physical.RadialLedger
