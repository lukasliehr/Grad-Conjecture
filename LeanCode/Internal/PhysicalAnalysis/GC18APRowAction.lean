import GC18APAllocation

noncomputable section

set_option maxHeartbeats 800000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.ClosedJets

def apSlotLinear {inputDimension outputDimension grade : ℕ}
    (outputIndex inputIndex : DerivativeIndex grade) (mapping : DiskL2 inputDimension →L[ℂ] DiskL2 outputDimension) :
    APRow inputDimension grade →ₗ[ℂ] APRow outputDimension grade where
  toFun field := PiLp.single 2 outputIndex (mapping (field inputIndex))
  map_add' first second := by
    change PiLp.single 2 (β := fun _ : DerivativeIndex grade => DiskL2 outputDimension)
      outputIndex (mapping (first inputIndex + second inputIndex)) = _
    rw [map_add, PiLp.single_add]
  map_smul' scalar field := by
    change PiLp.single 2 (β := fun _ : DerivativeIndex grade => DiskL2 outputDimension)
      outputIndex (mapping (scalar • field inputIndex)) = _
    rw [map_smul]
    simp only [PiLp.single, Pi.single_smul]
    rfl

theorem apSlotLinear_bound {inputDimension outputDimension grade : ℕ}
    (outputIndex inputIndex : DerivativeIndex grade) (mapping : DiskL2 inputDimension →L[ℂ] DiskL2 outputDimension)
    (field : APRow inputDimension grade) :
    ‖apSlotLinear outputIndex inputIndex mapping field‖ ≤ ‖mapping‖ * ‖field‖ := by
  change ‖PiLp.single 2 (β := fun _ : DerivativeIndex grade => DiskL2 outputDimension)
    outputIndex (mapping (field inputIndex))‖ ≤ _
  rw [PiLp.norm_single]
  exact (mapping.le_opNorm _).trans (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le field inputIndex) (norm_nonneg _))

def apSlotOperator {inputDimension outputDimension grade : ℕ}
    (outputIndex inputIndex : DerivativeIndex grade) (mapping : DiskL2 inputDimension →L[ℂ] DiskL2 outputDimension) :
    APRow inputDimension grade →L[ℂ] APRow outputDimension grade :=
  (apSlotLinear outputIndex inputIndex mapping).mkContinuous ‖mapping‖
    (apSlotLinear_bound outputIndex inputIndex mapping)

theorem apSlotOperator_norm_le {inputDimension outputDimension grade : ℕ}
    (outputIndex inputIndex : DerivativeIndex grade) (mapping : DiskL2 inputDimension →L[ℂ] DiskL2 outputDimension) :
    ‖apSlotOperator outputIndex inputIndex mapping‖ ≤ ‖mapping‖ :=
  (apSlotLinear outputIndex inputIndex mapping).mkContinuous_norm_le (norm_nonneg _)
    (apSlotLinear_bound outputIndex inputIndex mapping)

def apSingleKernel {inputDimension outputDimension grade : ℕ} (L sigma gamma ell : ℝ)
    (allocation : APAllocation grade) (shift : ℤ)
    (coefficient : C(ClosedDisk, OperatorValue inputDimension outputDimension)) (cell : ℤ) :
    APRow inputDimension grade →L[ℂ] APRow outputDimension grade :=
  apSlotOperator (apOutputIndex allocation) (apInputIndex allocation)
    (closedOperatorL2 (apKernelCoefficient L sigma gamma ell (derivativeOrder (apPhaseIndex allocation))
      (apPhaseWord allocation)
      (apCoefficientIndex allocation) (apInputIndex allocation) (cell - shift) shift coefficient))

theorem apSingleKernel_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ} (allocation : APAllocation grade) (shift : ℤ)
    (coefficient : C(ClosedDisk, OperatorValue inputDimension outputDimension)) (cell : ℤ) :
    ‖apSingleKernel L sigma gamma ell allocation shift coefficient cell‖ ≤
      apAllocationConstant L sigma gamma allocation * ‖coefficient‖ :=
  (apSlotOperator_norm_le _ _ _).trans ((closedOperatorL2_norm_le _).trans
    (apKernelCoefficient_norm_le admissible _ _ _ _ (apAllocation_order_le allocation) (cell - shift) shift coefficient))

/-- One Fourier shift of one genuine Leibniz allocation. No truncation of
the output cells occurs in this operator. -/
def apSingleOperator {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ} (allocation : APAllocation grade) (shift : ℤ)
    (coefficient : C(ClosedDisk, OperatorValue inputDimension outputDimension)) :
    APAmbient inputDimension grade →L[ℂ] APAmbient outputDimension grade :=
  apShiftOperator shift (apSingleKernel L sigma gamma ell allocation shift coefficient)
    (apAllocationConstant L sigma gamma allocation * ‖coefficient‖)
    (mul_nonneg (apAllocationConstant_nonnegative admissible allocation) (norm_nonneg coefficient))
    (apSingleKernel_bound admissible allocation shift coefficient)

theorem apSingleOperator_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension grade : ℕ} (allocation : APAllocation grade) (shift : ℤ)
    (coefficient : C(ClosedDisk, OperatorValue inputDimension outputDimension)) :
    ‖apSingleOperator admissible allocation shift coefficient‖ ≤
      apAllocationConstant L sigma gamma allocation * ‖coefficient‖ := by
  unfold apSingleOperator
  exact apShiftOperator_norm_le _ _ _ _ _

end Grad.GaugeCoefficients.Physical.RadialLedger
