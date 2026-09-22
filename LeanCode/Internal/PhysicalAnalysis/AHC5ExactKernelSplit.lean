import AHC4DistributedConvolutionBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Radial

theorem apDistributedRatio_cancel {grade : ℕ} (L sigma gamma ell : ℝ) (allocation : APAllocation grade)
    (input shift : ℤ) (point : ClosedDisk) :
    apDistributedRatio L sigma gamma ell allocation input shift point *
      (originalEnvelope sigma gamma ell shift point.val *
        (scaledCellWeight L ell shift + scaledCellWeight L ell input) ^ apDistributedOrder allocation) =
    scaledCellWeight L ell (input + shift) ^ (grade - derivativeOrder (apOutputIndex allocation)) *
      apRatioDerivative sigma gamma ell (derivativeOrder (apPhaseIndex allocation)) (apPhaseWord allocation) input shift point := by
  have denominatorNonzero : originalEnvelope sigma gamma ell shift point.val *
      (scaledCellWeight L ell shift + scaledCellWeight L ell input) ^ apDistributedOrder allocation ≠ 0 :=
    (mul_pos (Real.exp_pos _) (pow_pos (add_pos
      (lt_of_lt_of_le zero_lt_one (scaledCellWeight_one_le L ell shift))
      (lt_of_lt_of_le zero_lt_one (scaledCellWeight_one_le L ell input))) _)).ne'
  exact div_mul_cancel₀ _ denominatorNonzero

/-- The exact moment partition of the original kernel, including the phase
ratio. The coefficient and input spend complementary grades in every term. -/
theorem apDistributedScalar_sum {grade : ℕ} (L sigma gamma ell : ℝ) (allocation : APAllocation grade)
    (input shift : ℤ) (point : ClosedDisk) :
    (∑ moment : APDistributedMoment allocation,
      (Nat.choose (apDistributedOrder allocation) moment.val : ℂ) *
      (scaledCellWeight L ell input : ℂ) ^ (apDistributedInputGrade allocation moment -
        derivativeOrder (apDistributedInputIndex allocation moment)) *
      (apDistributedRatio L sigma gamma ell allocation input shift point : ℂ) *
      (coefficientScale L sigma gamma ell (apDistributedCoefficientGrade allocation moment) shift
        (apDistributedCoefficientIndex allocation moment) point : ℂ)) =
    (apKernelScalar L sigma gamma ell (derivativeOrder (apPhaseIndex allocation)) (apPhaseWord allocation)
      (apCoefficientIndex allocation) (apInputIndex allocation) input shift point : ℂ) *
    (coefficientScale L sigma gamma ell grade shift (apCoefficientIndex allocation) point : ℂ) *
      (scaledCellWeight L ell input : ℂ) ^ (grade - derivativeOrder (apInputIndex allocation)) := by
  have realIdentity :
      (∑ moment : APDistributedMoment allocation,
        (Nat.choose (apDistributedOrder allocation) moment.val : ℝ) *
        scaledCellWeight L ell input ^ (apDistributedInputGrade allocation moment -
          derivativeOrder (apDistributedInputIndex allocation moment)) *
        apDistributedRatio L sigma gamma ell allocation input shift point *
        coefficientScale L sigma gamma ell (apDistributedCoefficientGrade allocation moment) shift
          (apDistributedCoefficientIndex allocation moment) point) =
      scaledCellWeight L ell (input + shift) ^ (grade - derivativeOrder (apOutputIndex allocation)) *
        apRatioDerivative sigma gamma ell (derivativeOrder (apPhaseIndex allocation)) (apPhaseWord allocation) input shift point := by
    calc
      _ = apDistributedRatio L sigma gamma ell allocation input shift point *
          (∑ moment : APDistributedMoment allocation,
            (Nat.choose (apDistributedOrder allocation) moment.val : ℝ) *
            coefficientScale L sigma gamma ell (apDistributedCoefficientGrade allocation moment) shift
              (apDistributedCoefficientIndex allocation moment) point *
            scaledCellWeight L ell input ^ (apDistributedInputGrade allocation moment -
              derivativeOrder (apDistributedInputIndex allocation moment))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro moment _
        ring
      _ = _ := (congrArg (fun value : ℝ => apDistributedRatio L sigma gamma ell allocation input shift point * value)
        (apDistributedMoment_sum L sigma gamma ell allocation input shift point)).trans
          (apDistributedRatio_cancel L sigma gamma ell allocation input shift point)
  have casted := congrArg (fun value : ℝ => (value : ℂ)) realIdentity
  push_cast at casted
  exact casted.trans (apKernelScalar_cancel L sigma gamma ell input shift allocation point).symm

/-- Equality of continuous matrix kernels, using the actual coherent
coefficient derivatives. No independent coefficient array is substituted. -/
theorem apDistributedKernel_sum {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ}
    (allocation : APAllocation grade) (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (input shift : ℤ) :
    (∑ moment : APDistributedMoment allocation,
      (Nat.choose (apDistributedOrder allocation) moment.val : ℂ) •
        ((scaledCellWeight L ell input : ℂ) ^ (apDistributedInputGrade allocation moment -
          derivativeOrder (apDistributedInputIndex allocation moment))) •
        apDistributedKernelCoefficient L sigma gamma ell allocation input shift
          (weightedDerivative (family (apDistributedCoefficientGrade allocation moment)) shift
            (apDistributedCoefficientIndex allocation moment))) =
      ((scaledCellWeight L ell input : ℂ) ^ (grade - derivativeOrder (apInputIndex allocation))) •
        apKernelCoefficient L sigma gamma ell (derivativeOrder (apPhaseIndex allocation)) (apPhaseWord allocation)
          (apCoefficientIndex allocation) (apInputIndex allocation) input shift
          (weightedDerivative (family grade) shift (apCoefficientIndex allocation)) := by
  apply ContinuousMap.ext
  intro point
  have lowerValue (moment : APDistributedMoment allocation) :
      weightedDerivative (family (apDistributedCoefficientGrade allocation moment)) shift
          (apDistributedCoefficientIndex allocation moment) point =
        (coefficientScale L sigma gamma ell (apDistributedCoefficientGrade allocation moment) shift
          (apDistributedCoefficientIndex allocation moment) point : ℂ) •
          coefficientDerivative (family grade) shift (apCoefficientIndex allocation) point :=
    (weighted_derivative_literal _ inputDimension outputDimension
      (family (apDistributedCoefficientGrade allocation moment)) shift
        (apDistributedCoefficientIndex allocation moment) point).trans
      (congrArg (fun value : OperatorValue inputDimension outputDimension =>
        (coefficientScale L sigma gamma ell (apDistributedCoefficientGrade allocation moment) shift
          (apDistributedCoefficientIndex allocation moment) point : ℂ) • value)
        (coherent (apDistributedCoefficientGrade allocation moment) grade
          (apDistributedCoefficientIndex allocation moment) (apCoefficientIndex allocation) rfl shift point))
  rw [Grad.GaugeCoefficients.Radial.continuousMap_sum_apply]
  simp only [ContinuousMap.smul_apply]
  change (∑ moment : APDistributedMoment allocation,
    (Nat.choose (apDistributedOrder allocation) moment.val : ℂ) •
      ((scaledCellWeight L ell input : ℂ) ^ (apDistributedInputGrade allocation moment -
        derivativeOrder (apDistributedInputIndex allocation moment))) •
      ((apDistributedRatio L sigma gamma ell allocation input shift point : ℂ) •
        weightedDerivative (family (apDistributedCoefficientGrade allocation moment)) shift
          (apDistributedCoefficientIndex allocation moment) point)) = _
  simp_rw [lowerValue, smul_smul]
  rw [← Finset.sum_smul]
  have scalar := apDistributedScalar_sum L sigma gamma ell allocation input shift point
  simp only [mul_assoc] at scalar
  rw [scalar]
  change _ = ((scaledCellWeight L ell input : ℂ) ^ (grade - derivativeOrder (apInputIndex allocation))) •
    ((apKernelScalar L sigma gamma ell (derivativeOrder (apPhaseIndex allocation)) (apPhaseWord allocation)
      (apCoefficientIndex allocation) (apInputIndex allocation) input shift point : ℂ) •
      weightedDerivative (family grade) shift (apCoefficientIndex allocation) point)
  rw [weighted_derivative_literal grade inputDimension outputDimension (family grade) shift (apCoefficientIndex allocation) point]
  simp only [smul_smul]
  congr 1
  ring

end Grad.GaugeCoefficients.Physical.RadialLedger
