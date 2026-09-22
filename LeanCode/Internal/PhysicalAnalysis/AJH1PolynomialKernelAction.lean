import AJG14SamePhysicalInverseConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularRadialSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.BoundaryLift

/-- Polynomial coordinates used only for qualitative smoothness on a fixed
positive collar. The original weighted norms are retained separately. -/
def polynomialWeightRatio (power : ℕ) (shift mode : ℤ × ℤ) : ℝ :=
  annularFrequency mode.1 mode.2 ^ power /
    annularFrequency (twoFrequencyTranslation shift mode).1 (twoFrequencyTranslation shift mode).2 ^ power

theorem polynomialWeightRatio_nonnegative (power : ℕ) (shift mode : ℤ × ℤ) :
    0 ≤ polynomialWeightRatio power shift mode :=
  (div_pos (pow_pos (annularFrequency_pos mode) _) (pow_pos (annularFrequency_pos _) _)).le

theorem polynomialWeightRatio_bound (power : ℕ) (shift mode : ℤ × ℤ) :
    polynomialWeightRatio power shift mode ≤ annularFrequency shift.1 shift.2 ^ power := by
  rw [polynomialWeightRatio, div_le_iff₀ (pow_pos (annularFrequency_pos _) power)]
  have bound := pow_le_pow_left₀ (annularFrequency_pos mode).le (bulkFrequency_shift_le mode shift) power
  simpa only [mul_pow] using bound

variable {source target : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (kernel : FullTwoFrequencyKernel parameters source target)

def polynomialShiftEntry (shift mode : ℤ × ℤ) : ComplexEuclidean source →L[ℂ] ComplexEuclidean target :=
  (polynomialWeightRatio power shift mode : ℂ) • kernel.entry shift (twoFrequencyTranslation shift mode)

theorem polynomialShiftEntry_bound (shift mode : ℤ × ℤ) :
    ‖polynomialShiftEntry parameters power kernel shift mode‖ ≤
      annularFrequency shift.1 shift.2 ^ power * kernel.entryNorm shift := by
  apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
  rw [Complex.norm_real, Real.norm_of_nonneg (polynomialWeightRatio_nonnegative power shift mode)]
  exact mul_le_mul (polynomialWeightRatio_bound power shift mode) (kernel.entry_le shift _)
    (norm_nonneg _) (pow_nonneg (annularFrequency_pos shift).le _)

def polynomialShiftAction (shift : ℤ × ℤ) : CellL2 source →L[ℂ] CellL2 target :=
  coefficientOperator parameters 0 (twoFrequencyTranslation shift)
    (polynomialShiftEntry parameters power kernel shift)
    (mul_nonneg (pow_nonneg (annularFrequency_pos shift).le _) (fullKernelEntryNorm_nonnegative kernel shift))
    (polynomialShiftEntry_bound parameters power kernel shift)

theorem polynomialShiftAction_bound (shift : ℤ × ℤ) :
    ‖polynomialShiftAction parameters power kernel shift‖ ≤ annularFrequency shift.1 shift.2 ^ power * kernel.entryNorm shift :=
  coefficientOperator_norm_le parameters 0 (twoFrequencyTranslation shift) _ _ _

theorem polynomialKernelMajorant_summable :
    Summable (fun shift : ℤ × ℤ => annularFrequency shift.1 shift.2 ^ power * kernel.entryNorm shift) := by
  apply Summable.of_nonneg_of_le
    (fun shift => mul_nonneg (pow_nonneg (annularFrequency_pos shift).le _) (fullKernelEntryNorm_nonnegative kernel shift))
    (fun shift => ?_) (kernel.moments power)
  calc
    _ = 1 * (annularFrequency shift.1 shift.2 ^ power * kernel.entryNorm shift) := by rw [one_mul]
    _ ≤ boundaryCoefficientPhaseCost parameters shift * (annularFrequency shift.1 shift.2 ^ power * kernel.entryNorm shift) :=
      mul_le_mul_of_nonneg_right (boundaryCoefficientPhaseCost_one_le parameters shift)
        (mul_nonneg (pow_nonneg (annularFrequency_pos shift).le _) (fullKernelEntryNorm_nonnegative kernel shift))
    _ = _ := by ring

theorem polynomialShiftAction_summable : Summable (fun shift => polynomialShiftAction parameters power kernel shift) :=
  Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (polynomialShiftAction_bound parameters power kernel) (polynomialKernelMajorant_summable parameters power kernel))

/-- Reuse the accepted coefficientOperator and norm-convergent shift sum;
these are the literal same kernel entries in ordinary Sobolev coordinates. -/
def polynomialKernelAction : CellL2 source →L[ℂ] CellL2 target :=
  ∑' shift, polynomialShiftAction parameters power kernel shift

theorem polynomialKernelAction_bound :
    ‖polynomialKernelAction parameters power kernel‖ ≤ fullKernelMoment parameters power kernel := by
  have summable := polynomialKernelMajorant_summable parameters power kernel
  have norms := Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (polynomialShiftAction_bound parameters power kernel) summable
  apply (norm_tsum_le_tsum_norm norms).trans
  apply (norms.tsum_le_tsum (polynomialShiftAction_bound parameters power kernel) summable).trans
  apply summable.tsum_le_tsum _ (kernel.moments power)
  intro shift
  calc
    _ = 1 * (annularFrequency shift.1 shift.2 ^ power * kernel.entryNorm shift) := by rw [one_mul]
    _ ≤ boundaryCoefficientPhaseCost parameters shift * (annularFrequency shift.1 shift.2 ^ power * kernel.entryNorm shift) :=
      mul_le_mul_of_nonneg_right (boundaryCoefficientPhaseCost_one_le parameters shift)
        (mul_nonneg (pow_nonneg (annularFrequency_pos shift).le _) (fullKernelEntryNorm_nonnegative kernel shift))
    _ = _ := by ring

theorem polynomialKernelAction_coefficient (field : CellL2 source) (mode : ℤ × ℤ) :
    HasSum (fun shift => (polynomialWeightRatio power shift mode : ℂ) •
      kernel.entry shift (twoFrequencyTranslation shift mode) (field (twoFrequencyTranslation shift mode)))
      (polynomialKernelAction parameters power kernel field mode) := by
  have applied := (operatorEvaluation parameters 0 field).hasSum
    (polynomialShiftAction_summable parameters power kernel).hasSum
  exact (lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean target) 2 mode).hasSum applied

end Grad.AnnularRadialSmoothness
