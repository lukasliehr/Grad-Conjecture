import AHC5ExactKernelSplit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger
attribute [local instance] Grad.GaugeCoefficients.Physical.Compensated.apNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Compensated

/-- Exact lower-grade coordinate of the SAME completed input. -/
theorem apDistributedInput_coordinate {L sigma gamma ell : ℝ} {grade dimension : ℕ}
    (allocation : APAllocation grade) (moment : APDistributedMoment allocation) (cell : ℤ)
    (field : apGrade L sigma gamma ell dimension grade) :
    (apLowering L sigma gamma ell (apDistributed_grades allocation moment).2.2.2.2 field).val cell
        (apDistributedInputIndex allocation moment) =
      ((scaledCellWeight L ell cell : ℂ) ^ (apDistributedInputGrade allocation moment -
        derivativeOrder (apDistributedInputIndex allocation moment))) •
          apUnscaledCoordinate L sigma gamma ell cell (apInputIndex allocation) field :=
  (apCoordinate_eq_scaled L sigma gamma ell cell (apDistributedInputIndex allocation moment)
    (apLowering L sigma gamma ell (apDistributed_grades allocation moment).2.2.2.2 field)).trans
    (congrArg (fun value : DiskL2 dimension =>
      ((scaledCellWeight L ell cell : ℂ) ^ (apDistributedInputGrade allocation moment -
        derivativeOrder (apDistributedInputIndex allocation moment))) • value)
      (apUnscaledCoordinate_lowering L sigma gamma ell (apDistributed_grades allocation moment).2.2.2.2 cell
        (apDistributedInputIndex allocation moment) (apInputIndex allocation) rfl field))

theorem apDistributedKernelL2_sum {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ}
    (allocation : APAllocation grade) (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (input shift : ℤ)
    (field : apGrade L sigma gamma ell inputDimension grade) :
    (∑ moment : APDistributedMoment allocation,
      (Nat.choose (apDistributedOrder allocation) moment.val : ℂ) •
        closedOperatorL2 (apDistributedKernelCoefficient L sigma gamma ell allocation input shift
          (weightedDerivative (family (apDistributedCoefficientGrade allocation moment)) shift
            (apDistributedCoefficientIndex allocation moment)))
          ((apLowering L sigma gamma ell (apDistributed_grades allocation moment).2.2.2.2 field).val input
            (apDistributedInputIndex allocation moment))) =
      closedOperatorL2 (apKernelCoefficient L sigma gamma ell (derivativeOrder (apPhaseIndex allocation))
        (apPhaseWord allocation) (apCoefficientIndex allocation) (apInputIndex allocation) input shift
        (weightedDerivative (family grade) shift (apCoefficientIndex allocation)))
        (field.val input (apInputIndex allocation)) := by
  let raw := apUnscaledCoordinate L sigma gamma ell input (apInputIndex allocation) field
  let evaluation : C(ClosedDisk, OperatorValue inputDimension outputDimension) →L[ℂ] DiskL2 outputDimension :=
    (ContinuousLinearMap.apply ℂ (DiskL2 outputDimension) raw).comp (closedOperatorAction inputDimension outputDimension)
  have action := congrArg evaluation (apDistributedKernel_sum allocation family coherent input shift)
  simp only [map_sum, map_smul] at action
  simp_rw [apDistributedInput_coordinate allocation, map_smul]
  rw [apCoordinate_eq_scaled L sigma gamma ell input (apInputIndex allocation) field, map_smul]
  exact action

def apRowInsertLinear {dimension grade : ℕ} (index : DerivativeIndex grade) : DiskL2 dimension →ₗ[ℂ] APRow dimension grade where
  toFun value := PiLp.single 2 (β := fun _ : DerivativeIndex grade => DiskL2 dimension) index value
  map_add' first second := PiLp.single_add 2 index
  map_smul' scalar value := by
    simp only [PiLp.single, Pi.single_smul]
    rfl

/-- The existing original single-shift multiplier equals the distributed
moment sum on every completed input, proved from exact coordinates. -/
theorem apSingleOperator_distributed {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (allocation : APAllocation grade) (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (shift : ℤ)
    (field : apGrade L sigma gamma ell inputDimension grade) :
    apSingleOperator admissible allocation shift (weightedDerivative (family grade) shift (apCoefficientIndex allocation)) field.val =
      ∑ moment : APDistributedMoment allocation, (Nat.choose (apDistributedOrder allocation) moment.val : ℂ) •
        apDistributedSingleOperator admissible allocation moment shift
          (weightedDerivative (family (apDistributedCoefficientGrade allocation moment)) shift
            (apDistributedCoefficientIndex allocation moment))
          (apLowering L sigma gamma ell (apDistributed_grades allocation moment).2.2.2.2 field).val := by
  apply lp.ext
  funext cell
  let evaluation := lp.evalCLM ℂ (fun _ : ℤ => APRow outputDimension grade) 2 cell
  change apRowInsertLinear (apOutputIndex allocation)
    (closedOperatorL2 (apKernelCoefficient L sigma gamma ell (derivativeOrder (apPhaseIndex allocation))
      (apPhaseWord allocation) (apCoefficientIndex allocation) (apInputIndex allocation) (cell - shift) shift
      (weightedDerivative (family grade) shift (apCoefficientIndex allocation)))
      (field.val (cell - shift) (apInputIndex allocation))) = evaluation _
  rw [map_sum]
  simp only [map_smul]
  have rows := congrArg (apRowInsertLinear (dimension := outputDimension) (apOutputIndex allocation))
    (apDistributedKernelL2_sum allocation family coherent (cell - shift) shift field).symm
  simp only [map_sum, map_smul] at rows
  exact rows.trans (Finset.sum_congr rfl (fun moment _ => by
    congr 1))

end Grad.GaugeCoefficients.Physical.RadialLedger
