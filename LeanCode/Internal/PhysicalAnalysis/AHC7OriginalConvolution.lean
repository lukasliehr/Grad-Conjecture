import AHC6OriginalSingleShift

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger
attribute [local instance] Grad.GaugeCoefficients.Physical.Compensated.apNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.Allocation

theorem apDistributedAllocatedOperator_hasSum {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade input output : ℕ}
    (allocation : APAllocation grade) (moment : APDistributedMoment allocation)
    (coefficient : Coefficient L sigma gamma ell (apDistributedCoefficientGrade allocation moment) input output)
    (field : APAmbient input (apDistributedInputGrade allocation moment)) :
    HasSum (fun shift : ℤ => apDistributedSingleOperator admissible allocation moment shift
      (weightedDerivative coefficient shift (apDistributedCoefficientIndex allocation moment)) field)
      (apDistributedAllocatedOperator admissible allocation moment coefficient field) :=
  operatorHasSum_apply _ _
    (apDistributedSingle_norm_summable admissible allocation moment coefficient).of_norm.hasSum field

/-- The moment split sums to the original full-cell convolution on the
same completed input. Absolute operator summability justifies passage to the sum. -/
theorem apAllocatedOperator_distributed {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade input output : ℕ}
    (allocation : APAllocation grade) (family : CoefficientFamily L sigma gamma ell input output)
    (coherent : FamilyCoherent family) (field : apGrade L sigma gamma ell input grade) :
    apAllocatedOperator admissible allocation (family grade).val field.val =
      apDistributedAllocationValue admissible allocation family field := by
  have each (moment : APDistributedMoment allocation) :=
    (apDistributedAllocatedOperator_hasSum admissible allocation moment
      (family (apDistributedCoefficientGrade allocation moment))
      (apLowering L sigma gamma ell (apDistributed_grades allocation moment).2.2.2.2 field).val).const_smul
        (Nat.choose (apDistributedOrder allocation) moment.val : ℂ)
  have total := hasSum_sum (s := Finset.univ) (fun moment _ => each moment)
  have original := apAllocatedOperator_hasSum admissible allocation (family grade).val field.val
  apply original.unique
  exact total.congr_fun (fun shift => apSingleOperator_distributed admissible allocation family coherent shift field)

/-- Exact distributed identity for the existing multiplier at its original
width and all output cells, after passing to the original AP completion. -/
theorem apMultiplier_distributed {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (field : apGrade L sigma gamma ell input grade) :
    (apMultiplier admissible (family grade) field).val =
      ∑ allocation : APAllocation grade, (apMultiplicity allocation : ℂ) •
        apDistributedAllocationValue admissible allocation family field := by
  change apAmbientMultiplier admissible (family grade).val field.val = _
  simp only [apAmbientMultiplier, sum_apply, smul_apply]
  apply Finset.sum_congr rfl
  intro allocation _
  exact congrArg (fun value : APAmbient output grade => (apMultiplicity allocation : ℂ) • value)
    (apAllocatedOperator_distributed admissible allocation family coherent field)

end Grad.GaugeCoefficients.Physical.RadialLedger
