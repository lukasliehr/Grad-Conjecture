import GC18APCoreKernel
import GC10Core

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

theorem apSingleOperator_zero {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ} (allocation : APAllocation grade) (shift : ℤ) :
    apSingleOperator admissible allocation shift (0 : C(ClosedDisk, OperatorValue inputDimension outputDimension)) = 0 := by
  apply norm_le_zero_iff.mp
  have bound := apSingleOperator_bound admissible allocation shift
    (0 : C(ClosedDisk, OperatorValue inputDimension outputDimension))
  have zeroNorm : ‖(0 : C(ClosedDisk, OperatorValue inputDimension outputDimension))‖ = 0 :=
    @norm_zero (C(ClosedDisk, OperatorValue inputDimension outputDimension)) _
  rw [zeroNorm, mul_zero] at bound
  exact bound

theorem apAllocatedOperator_single {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ} (allocation : APAllocation grade) (shift : ℤ)
    (coefficient : SmoothOperatorJet inputDimension outputDimension) :
    apAllocatedOperator admissible allocation (weightedSingle L sigma gamma ell grade shift coefficient) =
      apSingleOperator admissible allocation shift
        (weightedSmoothDerivative L sigma gamma ell grade shift coefficient (apCoefficientIndex allocation)) := by
  unfold apAllocatedOperator
  rw [tsum_eq_single shift]
  · rw [weightedSingle_apply_same]
  · intro other different
    rw [weightedSingle_apply, if_neg different, apSingleOperator_zero]

theorem apSingleOperator_single {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ} (allocation : APAllocation grade) (input shift : ℤ)
    (coefficient : C(ClosedDisk, OperatorValue inputDimension outputDimension)) (field : ClosedJet inputDimension) :
    apSingleOperator admissible allocation shift coefficient (apSingle L sigma gamma ell input field) =
      lp.single 2 (input + shift) (apSingleKernel L sigma gamma ell allocation shift coefficient (input + shift)
        (apRowLinear L sigma gamma ell input field)) := by
  apply lp.ext
  funext cell
  change apSingleKernel L sigma gamma ell allocation shift coefficient cell
    ((lp.single 2 input (apRowLinear L sigma gamma ell input field) : APAmbient inputDimension grade) (cell - shift)) = _
  by_cases same : cell = input + shift
  · subst cell
    simp only [add_sub_cancel_right, lp.single_apply, Pi.single_eq_same]
  · have different : cell - shift ≠ input := by omega
    simp only [lp.single_apply, Pi.single_eq_of_ne different, Pi.single_eq_of_ne same, map_zero]

def apClosedL2Linear (dimension : ℕ) : C(ClosedDisk, ComplexEuclidean dimension) →ₗ[ℂ] DiskL2 dimension where
  toFun := closedContinuousToDiskL2
  map_add' := closedContinuousToDiskL2_add
  map_smul' := closedContinuousToDiskL2_smul

theorem apWeightedProduct_derivative_map {inputDimension outputDimension grade : ℕ} (sigma gamma ell : ℝ)
    (input shift : ℤ) (coefficient : SmoothOperatorJet inputDimension outputDimension)
    (field : ClosedJet inputDimension) (index : DerivativeIndex grade) :
    closedMultiDerivative (apWeightedJet sigma gamma ell (input + shift) (apProductJet coefficient field))
      (derivativeMultiIndex index) =
      ∑ firstSplit : DerivativeSplit index,
        ∑ secondSplit : DerivativeSplit (upperDerivativeIndex index firstSplit),
          (apMultiplicity ⟨index, firstSplit, secondSplit⟩ : ℂ) •
            apAllocationValue sigma gamma ell input shift coefficient field ⟨index, firstSplit, secondSplit⟩ := by
  apply ContinuousMap.ext
  intro point
  rw [apWeightedProduct_derivative]
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply]
  apply Finset.sum_congr rfl
  intro firstSplit _
  apply Finset.sum_congr rfl
  intro secondSplit _
  rfl

theorem apRowProduct_coordinate {inputDimension outputDimension grade : ℕ} (L sigma gamma ell : ℝ)
    (input shift : ℤ) (coefficient : SmoothOperatorJet inputDimension outputDimension)
    (field : ClosedJet inputDimension) (index : DerivativeIndex grade) :
    apDerivativeL2 L sigma gamma ell (input + shift) index (apProductJet coefficient field) =
      ∑ firstSplit : DerivativeSplit index,
        ∑ secondSplit : DerivativeSplit (upperDerivativeIndex index firstSplit),
          (apMultiplicity ⟨index, firstSplit, secondSplit⟩ : ℂ) •
            ((scaledCellWeight L ell (input + shift) : ℂ) ^ (grade - derivativeOrder index) •
              closedContinuousToDiskL2 (apAllocationValue sigma gamma ell input shift coefficient field ⟨index, firstSplit, secondSplit⟩)) := by
  change (scaledCellWeight L ell (input + shift) : ℂ) ^ (grade - derivativeOrder index) •
    apClosedL2Linear outputDimension (closedMultiDerivative
      (apWeightedJet sigma gamma ell (input + shift) (apProductJet coefficient field)) (derivativeMultiIndex index)) = _
  rw [apWeightedProduct_derivative_map]
  simp only [map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro firstSplit _
  apply Finset.sum_congr rfl
  intro secondSplit _
  exact smul_comm _ _ _

end Grad.GaugeCoefficients.Physical.RadialLedger
