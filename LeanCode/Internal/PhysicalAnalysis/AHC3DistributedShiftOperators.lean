import AHC2DistributedMomentKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.Allocation

/-- One needed row inclusion with independently assigned input/output grades. -/
def apMixedSlotLinear {input output low high : ℕ}
    (outputIndex : DerivativeIndex high) (inputIndex : DerivativeIndex low)
    (mapping : DiskL2 input →L[ℂ] DiskL2 output) : APRow input low →ₗ[ℂ] APRow output high where
  toFun field := PiLp.single 2 outputIndex (mapping (field inputIndex))
  map_add' first second := by
    change PiLp.single 2 (β := fun _ : DerivativeIndex high => DiskL2 output)
      outputIndex (mapping (first inputIndex + second inputIndex)) = _
    rw [map_add, PiLp.single_add]
  map_smul' scalar field := by
    change PiLp.single 2 (β := fun _ : DerivativeIndex high => DiskL2 output)
      outputIndex (mapping (scalar • field inputIndex)) = _
    rw [map_smul]
    simp only [PiLp.single, Pi.single_smul]
    rfl

theorem apMixedSlotLinear_bound {input output low high : ℕ}
    (outputIndex : DerivativeIndex high) (inputIndex : DerivativeIndex low)
    (mapping : DiskL2 input →L[ℂ] DiskL2 output) (field : APRow input low) :
    ‖apMixedSlotLinear outputIndex inputIndex mapping field‖ ≤ ‖mapping‖ * ‖field‖ := by
  change ‖PiLp.single 2 (β := fun _ : DerivativeIndex high => DiskL2 output)
    outputIndex (mapping (field inputIndex))‖ ≤ _
  rw [PiLp.norm_single]
  exact (mapping.le_opNorm _).trans (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le field inputIndex) (norm_nonneg _))

def apMixedSlotOperator {input output low high : ℕ}
    (outputIndex : DerivativeIndex high) (inputIndex : DerivativeIndex low)
    (mapping : DiskL2 input →L[ℂ] DiskL2 output) : APRow input low →L[ℂ] APRow output high :=
  (apMixedSlotLinear outputIndex inputIndex mapping).mkContinuous ‖mapping‖
    (apMixedSlotLinear_bound outputIndex inputIndex mapping)

theorem apMixedSlotOperator_norm_le {input output low high : ℕ}
    (outputIndex : DerivativeIndex high) (inputIndex : DerivativeIndex low)
    (mapping : DiskL2 input →L[ℂ] DiskL2 output) :
    ‖apMixedSlotOperator outputIndex inputIndex mapping‖ ≤ ‖mapping‖ :=
  (apMixedSlotLinear outputIndex inputIndex mapping).mkContinuous_norm_le (norm_nonneg _)
    (apMixedSlotLinear_bound outputIndex inputIndex mapping)

def apDistributedKernelCoefficient {grade inputDimension outputDimension : ℕ} (L sigma gamma ell : ℝ)
    (allocation : APAllocation grade) (input shift : ℤ)
    (coefficient : C(ClosedDisk, OperatorValue inputDimension outputDimension)) :
    C(ClosedDisk, OperatorValue inputDimension outputDimension) where
  toFun point := (apDistributedRatio L sigma gamma ell allocation input shift point : ℂ) • coefficient point
  continuous_toFun := (Complex.continuous_ofReal.comp
    (apDistributedRatio L sigma gamma ell allocation input shift).continuous).smul coefficient.continuous

theorem apDistributedKernelCoefficient_norm {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade inputDimension outputDimension : ℕ} (allocation : APAllocation grade) (input shift : ℤ)
    (coefficient : C(ClosedDisk, OperatorValue inputDimension outputDimension)) :
    ‖apDistributedKernelCoefficient L sigma gamma ell allocation input shift coefficient‖ ≤
      apRatioConstant L sigma gamma (derivativeOrder (apPhaseIndex allocation)) * ‖coefficient‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (apRatioConstant_nonnegative admissible (derivativeOrder (apPhaseIndex allocation))) (norm_nonneg coefficient))).mpr
  intro point
  change ‖(_ : ℂ) • coefficient point‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul (apDistributedRatio_bound admissible allocation input shift point)
    (ContinuousMap.norm_coe_le_norm coefficient point) (norm_nonneg (coefficient point))
      (apRatioConstant_nonnegative admissible (derivativeOrder (apPhaseIndex allocation)))

def apDistributedSingleKernel {grade inputDimension outputDimension : ℕ} (L sigma gamma ell : ℝ)
    (allocation : APAllocation grade) (moment : APDistributedMoment allocation) (shift : ℤ)
    (coefficient : C(ClosedDisk, OperatorValue inputDimension outputDimension)) (cell : ℤ) :
    APRow inputDimension (apDistributedInputGrade allocation moment) →L[ℂ] APRow outputDimension grade :=
  apMixedSlotOperator (apOutputIndex allocation) (apDistributedInputIndex allocation moment)
    (closedOperatorL2 (apDistributedKernelCoefficient L sigma gamma ell allocation (cell - shift) shift coefficient))

theorem apDistributedSingleKernel_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade inputDimension outputDimension : ℕ} (allocation : APAllocation grade)
    (moment : APDistributedMoment allocation) (shift : ℤ)
    (coefficient : C(ClosedDisk, OperatorValue inputDimension outputDimension)) (cell : ℤ) :
    ‖apDistributedSingleKernel L sigma gamma ell allocation moment shift coefficient cell‖ ≤
      apRatioConstant L sigma gamma (derivativeOrder (apPhaseIndex allocation)) * ‖coefficient‖ :=
  (apMixedSlotOperator_norm_le _ _ _).trans ((closedOperatorL2_norm_le _).trans
    (apDistributedKernelCoefficient_norm admissible allocation (cell - shift) shift coefficient))

/-- Full-cell shift, at the input grade complementary to the coefficient grade. -/
def apDistributedSingleOperator {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade inputDimension outputDimension : ℕ} (allocation : APAllocation grade)
    (moment : APDistributedMoment allocation) (shift : ℤ)
    (coefficient : C(ClosedDisk, OperatorValue inputDimension outputDimension)) :
    APAmbient inputDimension (apDistributedInputGrade allocation moment) →L[ℂ] APAmbient outputDimension grade :=
  apShiftOperator shift (apDistributedSingleKernel L sigma gamma ell allocation moment shift coefficient)
    (apRatioConstant L sigma gamma (derivativeOrder (apPhaseIndex allocation)) * ‖coefficient‖)
    (mul_nonneg (apRatioConstant_nonnegative admissible (derivativeOrder (apPhaseIndex allocation))) (norm_nonneg coefficient))
    (apDistributedSingleKernel_bound admissible allocation moment shift coefficient)

theorem apDistributedSingleOperator_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade inputDimension outputDimension : ℕ} (allocation : APAllocation grade)
    (moment : APDistributedMoment allocation) (shift : ℤ)
    (coefficient : C(ClosedDisk, OperatorValue inputDimension outputDimension)) :
    ‖apDistributedSingleOperator admissible allocation moment shift coefficient‖ ≤
      apRatioConstant L sigma gamma (derivativeOrder (apPhaseIndex allocation)) * ‖coefficient‖ :=
  apShiftOperator_norm_le _ _ _ _ _

end Grad.GaugeCoefficients.Physical.RadialLedger
