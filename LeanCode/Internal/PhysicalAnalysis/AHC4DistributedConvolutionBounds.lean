import AHC3DistributedShiftOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger
attribute [local instance] Grad.GaugeCoefficients.Physical.Compensated.apNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.Allocation

theorem apDistributedSingle_norm_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade input output : ℕ}
    (allocation : APAllocation grade) (moment : APDistributedMoment allocation)
    (coefficient : Coefficient L sigma gamma ell (apDistributedCoefficientGrade allocation moment) input output) :
    Summable (fun shift : ℤ => ‖apDistributedSingleOperator admissible allocation moment shift
      (weightedDerivative coefficient shift (apDistributedCoefficientIndex allocation moment))‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun shift => apDistributedSingleOperator_bound admissible allocation moment shift _)
    ((coordinate_norm_summable coefficient.val (apDistributedCoefficientIndex allocation moment)).mul_left
      (apRatioConstant L sigma gamma (derivativeOrder (apPhaseIndex allocation))))

/-- Original l1–l2 convolution, retaining every output cell. -/
def apDistributedAllocatedOperator {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade input output : ℕ}
    (allocation : APAllocation grade) (moment : APDistributedMoment allocation)
    (coefficient : Coefficient L sigma gamma ell (apDistributedCoefficientGrade allocation moment) input output) :
    APAmbient input (apDistributedInputGrade allocation moment) →L[ℂ] APAmbient output grade :=
  ∑' shift : ℤ, apDistributedSingleOperator admissible allocation moment shift
    (weightedDerivative coefficient shift (apDistributedCoefficientIndex allocation moment))

theorem apDistributedAllocatedOperator_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade input output : ℕ}
    (allocation : APAllocation grade) (moment : APDistributedMoment allocation)
    (coefficient : Coefficient L sigma gamma ell (apDistributedCoefficientGrade allocation moment) input output) :
    ‖apDistributedAllocatedOperator admissible allocation moment coefficient‖ ≤
      apRatioConstant L sigma gamma (derivativeOrder (apPhaseIndex allocation)) * ‖coefficient‖ := by
  have summable := apDistributedSingle_norm_summable admissible allocation moment coefficient
  apply (norm_tsum_le_tsum_norm summable).trans
  calc
    _ ≤ ∑' shift : ℤ, apRatioConstant L sigma gamma (derivativeOrder (apPhaseIndex allocation)) *
        ‖weightedDerivative coefficient shift (apDistributedCoefficientIndex allocation moment)‖ :=
      summable.tsum_le_tsum (fun shift => apDistributedSingleOperator_bound admissible allocation moment shift _)
        ((coordinate_norm_summable coefficient.val (apDistributedCoefficientIndex allocation moment)).mul_left _)
    _ = apRatioConstant L sigma gamma (derivativeOrder (apPhaseIndex allocation)) *
        ∑' shift : ℤ, ‖weightedDerivative coefficient shift (apDistributedCoefficientIndex allocation moment)‖ := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (coordinate_norm_sum_le coefficient.val (apDistributedCoefficientIndex allocation moment))
      (apRatioConstant_nonnegative admissible _)

def apDistributedGradeSum {L sigma gamma ell : ℝ} {input output grade : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (field : apGrade L sigma gamma ell input grade) : ℝ :=
  ∑ order : Fin (grade + 1), ‖family order.val‖ *
    ‖apLowering L sigma gamma ell (Nat.sub_le grade order.val) field‖

def apDistributedAllocationValue {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade input output : ℕ}
    (allocation : APAllocation grade) (family : CoefficientFamily L sigma gamma ell input output)
    (field : apGrade L sigma gamma ell input grade) : APAmbient output grade :=
  ∑ moment : APDistributedMoment allocation, (Nat.choose (apDistributedOrder allocation) moment.val : ℂ) •
    apDistributedAllocatedOperator admissible allocation moment
      (family (apDistributedCoefficientGrade allocation moment))
      (apLowering L sigma gamma ell (apDistributed_grades allocation moment).2.2.2.2 field).val

def apDistributedAllocationConstant {grade : ℕ} (L sigma gamma : ℝ) (allocation : APAllocation grade) : ℝ :=
  apRatioConstant L sigma gamma (derivativeOrder (apPhaseIndex allocation)) *
    ∑ moment : APDistributedMoment allocation, (Nat.choose (apDistributedOrder allocation) moment.val : ℝ)

theorem apDistributedAllocationValue_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade input output : ℕ}
    (allocation : APAllocation grade) (family : CoefficientFamily L sigma gamma ell input output)
    (field : apGrade L sigma gamma ell input grade) :
    ‖apDistributedAllocationValue admissible allocation family field‖ ≤
      apDistributedAllocationConstant L sigma gamma allocation * apDistributedGradeSum family field := by
  have momentBound (moment : APDistributedMoment allocation) :
      ‖apDistributedAllocatedOperator admissible allocation moment
        (family (apDistributedCoefficientGrade allocation moment))
        (apLowering L sigma gamma ell (apDistributed_grades allocation moment).2.2.2.2 field).val‖ ≤
      apRatioConstant L sigma gamma (derivativeOrder (apPhaseIndex allocation)) * apDistributedGradeSum family field := by
    have product := ((apDistributedAllocatedOperator admissible allocation moment
      (family (apDistributedCoefficientGrade allocation moment))).le_opNorm
        (apLowering L sigma gamma ell (apDistributed_grades allocation moment).2.2.2.2 field).val).trans
      (mul_le_mul_of_nonneg_right (apDistributedAllocatedOperator_bound admissible allocation moment
        (family (apDistributedCoefficientGrade allocation moment))) (norm_nonneg _))
    have selected := Finset.single_le_sum
      (f := fun order : Fin (grade + 1) => ‖family order.val‖ *
        ‖apLowering L sigma gamma ell (Nat.sub_le grade order.val) field‖)
      (s := Finset.univ) (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (Finset.mem_univ (⟨apDistributedCoefficientGrade allocation moment,
        Nat.lt_succ_of_le (apDistributed_grades allocation moment).2.2.2.1⟩ : Fin (grade + 1)))
    exact product.trans ((mul_assoc _ _ _).le.trans
      (mul_le_mul_of_nonneg_left selected (apRatioConstant_nonnegative admissible _)))
  apply (norm_sum_le _ _).trans
  calc
    _ = ∑ moment : APDistributedMoment allocation, (Nat.choose (apDistributedOrder allocation) moment.val : ℝ) *
        ‖apDistributedAllocatedOperator admissible allocation moment
          (family (apDistributedCoefficientGrade allocation moment))
          (apLowering L sigma gamma ell (apDistributed_grades allocation moment).2.2.2.2 field).val‖ := by
      apply Finset.sum_congr rfl
      intro moment _
      rw [norm_smul, Complex.norm_natCast]
    _ ≤ ∑ moment : APDistributedMoment allocation, (Nat.choose (apDistributedOrder allocation) moment.val : ℝ) *
        (apRatioConstant L sigma gamma (derivativeOrder (apPhaseIndex allocation)) * apDistributedGradeSum family field) :=
      Finset.sum_le_sum (fun moment _ => mul_le_mul_of_nonneg_left (momentBound moment) (Nat.cast_nonneg _))
    _ = _ := by
      unfold apDistributedAllocationConstant
      rw [← Finset.sum_mul]
      ring

end Grad.GaugeCoefficients.Physical.RadialLedger
