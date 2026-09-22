import GC18APSeries

noncomputable section

set_option maxHeartbeats 800000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

theorem apKernelCoefficient_add {grade inputDimension outputDimension : ℕ} (L sigma gamma ell : ℝ)
    (rank : ℕ) (word : Fin rank → Fin 2) (coefficientIndex inputIndex : DerivativeIndex grade) (input shift : ℤ)
    (first second : C(ClosedDisk, OperatorValue inputDimension outputDimension)) :
    apKernelCoefficient L sigma gamma ell rank word coefficientIndex inputIndex input shift (first + second) =
      apKernelCoefficient L sigma gamma ell rank word coefficientIndex inputIndex input shift first +
        apKernelCoefficient L sigma gamma ell rank word coefficientIndex inputIndex input shift second := by
  apply ContinuousMap.ext
  intro point
  exact smul_add _ _ _

theorem apKernelCoefficient_smul {grade inputDimension outputDimension : ℕ} (L sigma gamma ell : ℝ)
    (rank : ℕ) (word : Fin rank → Fin 2) (coefficientIndex inputIndex : DerivativeIndex grade) (input shift : ℤ)
    (scalar : ℂ) (coefficient : C(ClosedDisk, OperatorValue inputDimension outputDimension)) :
    apKernelCoefficient L sigma gamma ell rank word coefficientIndex inputIndex input shift (scalar • coefficient) =
      scalar • apKernelCoefficient L sigma gamma ell rank word coefficientIndex inputIndex input shift coefficient := by
  apply ContinuousMap.ext
  intro point
  exact smul_comm (apKernelScalar L sigma gamma ell rank word coefficientIndex inputIndex input shift point : ℂ)
    scalar (coefficient point)

theorem apSlotOperator_add {inputDimension outputDimension grade : ℕ} (outputIndex inputIndex : DerivativeIndex grade)
    (first second : DiskL2 inputDimension →L[ℂ] DiskL2 outputDimension) :
    apSlotOperator outputIndex inputIndex (first + second) = apSlotOperator outputIndex inputIndex first +
      apSlotOperator outputIndex inputIndex second := by
  apply ContinuousLinearMap.ext
  intro field
  change PiLp.single 2 (β := fun _ : DerivativeIndex grade => DiskL2 outputDimension)
    outputIndex (first (field inputIndex) + second (field inputIndex)) = _
  exact PiLp.single_add 2 outputIndex

theorem apSlotOperator_smul {inputDimension outputDimension grade : ℕ} (outputIndex inputIndex : DerivativeIndex grade)
    (scalar : ℂ) (mapping : DiskL2 inputDimension →L[ℂ] DiskL2 outputDimension) :
    apSlotOperator outputIndex inputIndex (scalar • mapping) = scalar • apSlotOperator outputIndex inputIndex mapping := by
  apply ContinuousLinearMap.ext
  intro field
  change PiLp.single 2 (β := fun _ : DerivativeIndex grade => DiskL2 outputDimension)
    outputIndex (scalar • mapping (field inputIndex)) = _
  simp only [PiLp.single, Pi.single_smul]
  rfl

theorem apSingleKernel_add {inputDimension outputDimension grade : ℕ} (L sigma gamma ell : ℝ)
    (allocation : APAllocation grade) (shift : ℤ) (first second : C(ClosedDisk, OperatorValue inputDimension outputDimension))
    (cell : ℤ) :
    apSingleKernel L sigma gamma ell allocation shift (first + second) cell =
      apSingleKernel L sigma gamma ell allocation shift first cell + apSingleKernel L sigma gamma ell allocation shift second cell := by
  rw [apSingleKernel, apKernelCoefficient_add, closedOperatorL2_add, apSlotOperator_add]
  rfl

theorem apSingleKernel_smul {inputDimension outputDimension grade : ℕ} (L sigma gamma ell : ℝ)
    (allocation : APAllocation grade) (shift : ℤ) (scalar : ℂ)
    (coefficient : C(ClosedDisk, OperatorValue inputDimension outputDimension)) (cell : ℤ) :
    apSingleKernel L sigma gamma ell allocation shift (scalar • coefficient) cell =
      scalar • apSingleKernel L sigma gamma ell allocation shift coefficient cell := by
  rw [apSingleKernel, apKernelCoefficient_smul, closedOperatorL2_smul, apSlotOperator_smul]
  rfl

theorem apSingleOperator_add {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ} (allocation : APAllocation grade) (shift : ℤ)
    (first second : C(ClosedDisk, OperatorValue inputDimension outputDimension)) :
    apSingleOperator admissible allocation shift (first + second) =
      apSingleOperator admissible allocation shift first + apSingleOperator admissible allocation shift second := by
  apply ContinuousLinearMap.ext
  intro field
  apply lp.ext
  funext cell
  change apSingleKernel L sigma gamma ell allocation shift (first + second) cell (field (cell - shift)) =
    apSingleKernel L sigma gamma ell allocation shift first cell (field (cell - shift)) +
      apSingleKernel L sigma gamma ell allocation shift second cell (field (cell - shift))
  rw [apSingleKernel_add, add_apply]

theorem apSingleOperator_smul {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ} (allocation : APAllocation grade) (shift : ℤ)
    (scalar : ℂ) (coefficient : C(ClosedDisk, OperatorValue inputDimension outputDimension)) :
    apSingleOperator admissible allocation shift (scalar • coefficient) = scalar • apSingleOperator admissible allocation shift coefficient := by
  apply ContinuousLinearMap.ext
  intro field
  apply lp.ext
  funext cell
  change apSingleKernel L sigma gamma ell allocation shift (scalar • coefficient) cell (field (cell - shift)) =
    scalar • apSingleKernel L sigma gamma ell allocation shift coefficient cell (field (cell - shift))
  rw [apSingleKernel_smul, smul_apply]

end Grad.GaugeCoefficients.Physical.RadialLedger
