import GC18APCoreSeries
import GC18APCoreRows

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

theorem apSingleKernel_core {inputDimension outputDimension grade : ℕ} (L sigma gamma ell : ℝ)
    (input shift : ℤ) (coefficient : SmoothOperatorJet inputDimension outputDimension)
    (field : ClosedJet inputDimension) (allocation : APAllocation grade) :
    apSingleKernel L sigma gamma ell allocation shift
      (weightedSmoothDerivative L sigma gamma ell grade shift coefficient (apCoefficientIndex allocation)) (input + shift)
      (apRowLinear L sigma gamma ell input field) =
      PiLp.single 2 (apOutputIndex allocation)
        ((scaledCellWeight L ell (input + shift) : ℂ) ^ (grade - derivativeOrder (apOutputIndex allocation)) •
          closedContinuousToDiskL2 (apAllocationValue sigma gamma ell input shift coefficient field allocation)) := by
  unfold apSingleKernel
  simp only [add_sub_cancel_right]
  change PiLp.single 2 (β := fun _ : DerivativeIndex grade => DiskL2 outputDimension) (apOutputIndex allocation)
    (closedOperatorL2 _ (apDerivativeL2 L sigma gamma ell input (apInputIndex allocation) field)) = _
  rw [apCoreKernel_l2]

theorem apKernelRow_product {inputDimension outputDimension grade : ℕ} (L sigma gamma ell : ℝ)
    (input shift : ℤ) (coefficient : SmoothOperatorJet inputDimension outputDimension) (field : ClosedJet inputDimension) :
    (∑ allocation : APAllocation grade, (apMultiplicity allocation : ℂ) •
      apSingleKernel L sigma gamma ell allocation shift
        (weightedSmoothDerivative L sigma gamma ell grade shift coefficient (apCoefficientIndex allocation)) (input + shift)
        (apRowLinear L sigma gamma ell input field)) =
      apRowLinear L sigma gamma ell (input + shift) (apProductJet coefficient field) := by
  simp_rw [apSingleKernel_core, apSingleRow_smul]
  apply PiLp.ext
  intro index
  rw [apAllocation_single_sum]
  exact (apRowProduct_coordinate L sigma gamma ell input shift coefficient field index).symm

def apCellInjectionLinear (dimension grade : ℕ) (cell : ℤ) : APRow dimension grade →ₗ[ℂ] APAmbient dimension grade where
  toFun row := lp.single 2 cell row
  map_add' first second := by
    apply lp.ext
    funext other
    simp only [lp.single_apply, lp.coeFn_add, Pi.add_apply, Pi.single_apply]
    split_ifs <;> simp
  map_smul' scalar row := by
    apply lp.ext
    funext other
    simp only [lp.single_apply, lp.coeFn_smul, Pi.smul_apply, Pi.single_apply]
    split_ifs <;> simp

/-- Literal finite-cell product in the unchanged AP2 norm. Both the output
cell and every Cartesian derivative are the genuine product coordinates. -/
theorem apAmbientMultiplier_core {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ} (input shift : ℤ)
    (coefficient : SmoothOperatorJet inputDimension outputDimension) (field : ClosedJet inputDimension) :
    apAmbientMultiplier admissible (weightedSingle L sigma gamma ell grade shift coefficient)
      (apSingle L sigma gamma ell input field) =
      apSingle L sigma gamma ell (input + shift) (apProductJet coefficient field) := by
  unfold apAmbientMultiplier
  simp only [sum_apply, smul_apply, apAllocatedOperator_single, apSingleOperator_single]
  change (∑ allocation : APAllocation grade, (apMultiplicity allocation : ℂ) •
    apCellInjectionLinear outputDimension grade (input + shift)
      (apSingleKernel L sigma gamma ell allocation shift
        (weightedSmoothDerivative L sigma gamma ell grade shift coefficient (apCoefficientIndex allocation)) (input + shift)
        (apRowLinear L sigma gamma ell input field))) =
    apCellInjectionLinear outputDimension grade (input + shift)
      (apRowLinear L sigma gamma ell (input + shift) (apProductJet coefficient field))
  simp only [← (apCellInjectionLinear outputDimension grade (input + shift)).map_smul]
  rw [← map_sum, apKernelRow_product]

end Grad.GaugeCoefficients.Physical.RadialLedger
