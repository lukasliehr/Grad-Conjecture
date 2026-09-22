import AKCD1BalancedNativeKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularKernelL2

theorem nativeBalance_weighted (parameters : PhaseParameters) (grade : ℕ) (radius : ℝ)
    (shift mode : ℤ × ℤ) :
    bulkWeightRatio parameters grade radius shift mode *
      annularFrequency (twoFrequencyTranslation shift mode).1 (twoFrequencyTranslation shift mode).2 ^ grade =
    bulkWeightRatio parameters 0 radius shift mode * nativeBalance grade shift (twoFrequencyTranslation shift mode) *
      (annularFrequency (twoFrequencyTranslation shift mode).1 (twoFrequencyTranslation shift mode).2 ^ grade +
        annularFrequency shift.1 shift.2 ^ grade) := by
  have positive := pow_pos (annularFrequency_pos (twoFrequencyTranslation shift mode)) grade
  have denominator := add_pos positive (pow_pos (annularFrequency_pos shift) grade)
  have translated : twoFrequencyTranslation shift mode + shift = mode := by
    ext <;> simp [twoFrequencyTranslation]
  simp only [bulkWeightRatio,nativeBalance,translated,pow_zero,mul_one,div_one]
  field_simp

theorem nativeBalancedAction_same {input output : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (radius : RadialPoint) (kernel : RadialKernel parameters radius input output)
    (high low : CellL2 input)
    (same : ∀ mode, high mode = (annularFrequency mode.1 mode.2 : ℂ)^grade • low mode) :
    bulkKernelAction parameters grade radius kernel high =
      bulkKernelAction parameters 0 radius (nativeBalancedKernel kernel grade 0) high +
      bulkKernelAction parameters 0 radius (nativeBalancedKernel kernel grade grade) low := by
  apply lp.ext
  funext mode
  apply (bulkKernelAction_coordinate parameters grade radius kernel high mode).unique
  have total := (bulkKernelAction_coordinate parameters 0 radius (nativeBalancedKernel kernel grade 0) high mode).add
    (bulkKernelAction_coordinate parameters 0 radius (nativeBalancedKernel kernel grade grade) low mode)
  apply total.congr_fun
  intro shift
  simp only [nativeBalancedKernel,fullKernelOfEntries_entry,nativeBalancedEntry,
    _root_.smul_apply,same,map_smul,smul_smul,pow_zero,one_mul]
  rw [← add_smul]
  congr 1
  have weighted := nativeBalance_weighted parameters grade radius.val shift mode
  have scalar := congrArg (fun value : ℝ => (value:ℂ)) weighted
  push_cast at scalar ⊢
  linear_combination scalar

/-- Exact two-input estimate for the SAME bulk Fourier action. The high
coefficient moment multiplies only the compatible zeroth-grade input. -/
theorem nativeBalancedAction_bound {input output : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (radius : RadialPoint) (kernel : RadialKernel parameters radius input output)
    (high low : CellL2 input)
    (same : ∀ mode, high mode = (annularFrequency mode.1 mode.2 : ℂ)^grade • low mode) :
    ‖bulkKernelAction parameters grade radius kernel high‖ ≤
      2 ^ grade * (fullKernelMoment (radialKernelParameters parameters radius) 0 kernel * ‖high‖ +
        fullKernelMoment (radialKernelParameters parameters radius) grade kernel * ‖low‖) := by
  rw [nativeBalancedAction_same parameters grade radius kernel high low same]
  apply (norm_add_le _ _).trans
  have first := (bulkKernelAction_bound parameters 0 radius (nativeBalancedKernel kernel grade 0) high).trans
    (mul_le_mul_of_nonneg_right (nativeBalancedKernel_moment kernel grade 0 0) (norm_nonneg _))
  have second := (bulkKernelAction_bound parameters 0 radius (nativeBalancedKernel kernel grade grade) low).trans
    (mul_le_mul_of_nonneg_right (nativeBalancedKernel_moment kernel grade grade 0) (norm_nonneg _))
  exact (add_le_add first second).trans_eq (by simp only [Nat.zero_add]; ring)

end Grad.OriginalCartesianTameEstimate
