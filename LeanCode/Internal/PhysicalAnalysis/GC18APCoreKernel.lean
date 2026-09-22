import GC18APWeightedProduct
import GC18APBilinear

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

def apAllocationValue {inputDimension outputDimension grade : ℕ} (sigma gamma ell : ℝ)
    (input shift : ℤ) (coefficient : SmoothOperatorJet inputDimension outputDimension)
    (field : ClosedJet inputDimension) (allocation : APAllocation grade) : C(ClosedDisk, ComplexEuclidean outputDimension) where
  toFun point := (apRatioDerivative sigma gamma ell (derivativeOrder (apPhaseIndex allocation))
    (apPhaseWord allocation) input shift point : ℂ) •
    smoothOperatorDerivative coefficient (derivativeMultiIndex (apCoefficientIndex allocation)) point
      (closedMultiDerivative (apWeightedJet sigma gamma ell input field) (derivativeMultiIndex (apInputIndex allocation)) point)
  continuous_toFun := (Complex.continuous_ofReal.comp (apRatioDerivative sigma gamma ell
    (derivativeOrder (apPhaseIndex allocation)) (apPhaseWord allocation) input shift).continuous).smul
      ((smoothOperatorDerivative coefficient _).continuous.clm_apply (closedMultiDerivative _ _).continuous)

theorem apKernelScalar_cancel {grade : ℕ} (L sigma gamma ell : ℝ)
    (input shift : ℤ) (allocation : APAllocation grade) (point : ClosedDisk) :
    (apKernelScalar L sigma gamma ell (derivativeOrder (apPhaseIndex allocation)) (apPhaseWord allocation)
      (apCoefficientIndex allocation) (apInputIndex allocation) input shift point : ℂ) *
        (coefficientScale L sigma gamma ell grade shift (apCoefficientIndex allocation) point : ℂ) *
        (scaledCellWeight L ell input : ℂ) ^ (grade - derivativeOrder (apInputIndex allocation)) =
      (scaledCellWeight L ell (input + shift) : ℂ) ^ (grade - derivativeOrder (apOutputIndex allocation)) *
        (apRatioDerivative sigma gamma ell (derivativeOrder (apPhaseIndex allocation))
          (apPhaseWord allocation) input shift point : ℂ) := by
  have scaleNonzero : (coefficientScale L sigma gamma ell grade shift (apCoefficientIndex allocation) point : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (coefficientScale_pos L sigma gamma ell grade shift (apCoefficientIndex allocation) point).ne'
  have inputNonzero : (scaledCellWeight L ell input : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le zero_lt_one (scaledCellWeight_one_le L ell input)).ne'
  dsimp only [apKernelScalar, ContinuousMap.coe_mk]
  rw [apAllocation_order]
  push_cast
  field_simp

theorem apCoreKernel_value {inputDimension outputDimension grade : ℕ} (L sigma gamma ell : ℝ)
    (input shift : ℤ) (coefficient : SmoothOperatorJet inputDimension outputDimension)
    (field : ClosedJet inputDimension) (allocation : APAllocation grade) (point : ClosedDisk) :
    apKernelCoefficient L sigma gamma ell (derivativeOrder (apPhaseIndex allocation)) (apPhaseWord allocation)
      (apCoefficientIndex allocation) (apInputIndex allocation) input shift
      (weightedSmoothDerivative L sigma gamma ell grade shift coefficient (apCoefficientIndex allocation)) point
      ((scaledCellWeight L ell input : ℂ) ^ (grade - derivativeOrder (apInputIndex allocation)) •
        closedMultiDerivative (apWeightedJet sigma gamma ell input field) (derivativeMultiIndex (apInputIndex allocation)) point) =
    (scaledCellWeight L ell (input + shift) : ℂ) ^ (grade - derivativeOrder (apOutputIndex allocation)) •
      apAllocationValue sigma gamma ell input shift coefficient field allocation point := by
  dsimp only [apKernelCoefficient, weightedSmoothDerivative, ContinuousMap.coe_mk, apAllocationValue]
  rw [smul_apply, smul_apply, map_smul]
  simp only [smul_smul]
  rw [← mul_assoc, apKernelScalar_cancel]

theorem apCoreKernel_l2 {inputDimension outputDimension grade : ℕ} (L sigma gamma ell : ℝ)
    (input shift : ℤ) (coefficient : SmoothOperatorJet inputDimension outputDimension)
    (field : ClosedJet inputDimension) (allocation : APAllocation grade) :
    closedOperatorL2 (apKernelCoefficient L sigma gamma ell (derivativeOrder (apPhaseIndex allocation)) (apPhaseWord allocation)
      (apCoefficientIndex allocation) (apInputIndex allocation) input shift
      (weightedSmoothDerivative L sigma gamma ell grade shift coefficient (apCoefficientIndex allocation)))
      (apDerivativeL2 L sigma gamma ell input (apInputIndex allocation) field) =
    (scaledCellWeight L ell (input + shift) : ℂ) ^ (grade - derivativeOrder (apOutputIndex allocation)) •
      closedContinuousToDiskL2 (apAllocationValue sigma gamma ell input shift coefficient field allocation) := by
  change closedOperatorL2 _ ((scaledCellWeight L ell input : ℂ) ^ (grade - derivativeOrder (apInputIndex allocation)) •
    closedContinuousToDiskL2 (closedMultiDerivative (apWeightedJet sigma gamma ell input field)
      (derivativeMultiIndex (apInputIndex allocation)))) = _
  rw [← closedContinuousToDiskL2_smul, closedOperatorL2_closed, ← closedContinuousToDiskL2_smul]
  congr 1
  apply ContinuousMap.ext
  intro point
  exact apCoreKernel_value L sigma gamma ell input shift coefficient field allocation point

end Grad.GaugeCoefficients.Physical.RadialLedger
