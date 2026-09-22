import AHC7OriginalConvolution

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger
attribute [local instance] Grad.GaugeCoefficients.Physical.Compensated.apNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.Allocation

/-- Depends only on the fixed width parameters and derivative grade,
not on the collar scale or cell index. -/
def apDistributedMultiplierConstant (L sigma gamma : ℝ) (grade : ℕ) : ℝ :=
  ∑ allocation : APAllocation grade, (apMultiplicity allocation : ℝ) *
    apDistributedAllocationConstant L sigma gamma allocation

theorem apDistributedMultiplierConstant_nonnegative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    0 ≤ apDistributedMultiplierConstant L sigma gamma grade := by
  apply Finset.sum_nonneg
  intro allocation _
  exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (apRatioConstant_nonnegative admissible _)
    (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)))

/-- AQ20--23: the original completed cap multiplier spends complementary
coefficient and field grades. The sum includes every coefficient grade,
uses the actual lowering of the same input, and retains the original width. -/
theorem apMultiplier_distributed_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (field : apGrade L sigma gamma ell input grade) :
    ‖apMultiplier admissible (family grade) field‖ ≤
      apDistributedMultiplierConstant L sigma gamma grade *
        ∑ order : Fin (grade + 1), ‖family order.val‖ *
          ‖apLowering L sigma gamma ell (Nat.sub_le grade order.val) field‖ := by
  change ‖(apMultiplier admissible (family grade) field).val‖ ≤ _
  rw [apMultiplier_distributed admissible family coherent field]
  apply (norm_sum_le _ _).trans
  calc
    _ = ∑ allocation : APAllocation grade, (apMultiplicity allocation : ℝ) *
        ‖apDistributedAllocationValue admissible allocation family field‖ := by
      apply Finset.sum_congr rfl
      intro allocation _
      rw [norm_smul, Complex.norm_natCast]
    _ ≤ ∑ allocation : APAllocation grade, (apMultiplicity allocation : ℝ) *
        (apDistributedAllocationConstant L sigma gamma allocation * apDistributedGradeSum family field) :=
      Finset.sum_le_sum (fun allocation _ => mul_le_mul_of_nonneg_left
        (apDistributedAllocationValue_bound admissible allocation family field) (Nat.cast_nonneg _))
    _ = _ := by
      unfold apDistributedMultiplierConstant apDistributedGradeSum
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro allocation _
      ring

end Grad.GaugeCoefficients.Physical.RadialLedger
