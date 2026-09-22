import AKDH8OrderedBalancedEulerRecurrence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularWeightedSmoothness
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.Allocation

/-- Actual phase Euler jet with its original exponential ratio factored
out. This keeps the original kernel algebra, with displacement cost only. -/
def phaseEulerMultiplier (parameters : PhaseParameters) (rank : ℕ) (radius : RadialPoint)
    (shift input : ℤ × ℤ) : ℝ :=
  eulerIteratedDerivative rank
    (radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2) radius.val /
      radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2 radius.val

theorem phaseEulerMultiplier_bound (parameters : PhaseParameters) (rank : ℕ) (radius : RadialPoint)
    (shift input : ℤ × ℤ) :
    ‖phaseEulerMultiplier parameters rank radius shift input‖ ≤
      positiveEulerRatioConstant parameters rank * annularFrequency shift.1 shift.2^rank := by
  have positive : 0 < radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2 radius.val := Real.exp_pos _
  rw [phaseEulerMultiplier,norm_div,Real.norm_of_nonneg positive.le,div_le_iff₀ positive]
  exact (radialPhaseRatio_euler_displacement parameters rank shift input radius).trans_eq (by ring_nf; rfl)

def phaseEulerKernelEntry {source target : ℕ} (parameters : PhaseParameters) (radius : RadialPoint)
    (rank : ℕ) (kernel : RadialKernel parameters radius source target) (shift input : ℤ × ℤ) :=
  (phaseEulerMultiplier parameters rank radius shift input : ℂ) • kernel.entry shift input

theorem phaseEulerKernelEntry_bound {source target : ℕ} (parameters : PhaseParameters) (radius : RadialPoint)
    (rank : ℕ) (kernel : RadialKernel parameters radius source target) (shift input : ℤ × ℤ) :
    ‖phaseEulerKernelEntry parameters radius rank kernel shift input‖ ≤
      positiveEulerRatioConstant parameters rank * annularFrequency shift.1 shift.2^rank * kernel.entryNorm shift := by
  apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
  rw [Complex.norm_real]
  exact mul_le_mul (phaseEulerMultiplier_bound parameters rank radius shift input) (kernel.entry_le shift input)
    (norm_nonneg _) (mul_nonneg (zero_le_one.trans (positiveEulerRatioConstant_one_le parameters rank))
      (pow_nonneg (annularFrequency_pos shift).le rank))

theorem phaseEulerKernelEntry_moments {source target : ℕ} (parameters : PhaseParameters) (radius : RadialPoint)
    (rank : ℕ) (kernel : RadialKernel parameters radius source target) (moment : ℕ) :
    Summable (fun shift : ℤ × ℤ => boundaryCoefficientPhaseCost (radialKernelParameters parameters radius) shift *
      annularFrequency shift.1 shift.2^moment *
        (positiveEulerRatioConstant parameters rank * annularFrequency shift.1 shift.2^rank * kernel.entryNorm shift)) := by
  apply ((kernel.moments (moment+rank)).mul_left (positiveEulerRatioConstant parameters rank)).congr
  intro shift
  rw [pow_add]
  ring

def phaseEulerKernel {source target : ℕ} (parameters : PhaseParameters) (radius : RadialPoint)
    (rank : ℕ) (kernel : RadialKernel parameters radius source target) : RadialKernel parameters radius source target :=
  fullKernelOfEntries (radialKernelParameters parameters radius) (phaseEulerKernelEntry parameters radius rank kernel)
    (fun shift => positiveEulerRatioConstant parameters rank * annularFrequency shift.1 shift.2^rank * kernel.entryNorm shift)
    (phaseEulerKernelEntry_bound parameters radius rank kernel) (phaseEulerKernelEntry_moments parameters radius rank kernel)

theorem phaseEulerKernel_moment {source target : ℕ} (parameters : PhaseParameters) (radius : RadialPoint)
    (rank moment : ℕ) (kernel : RadialKernel parameters radius source target) :
    fullKernelMoment (radialKernelParameters parameters radius) moment (phaseEulerKernel parameters radius rank kernel) ≤
      positiveEulerRatioConstant parameters rank * fullKernelMoment (radialKernelParameters parameters radius) (moment+rank) kernel := by
  apply ((phaseEulerKernel parameters radius rank kernel).moments moment).tsum_le_tsum
    (fun shift => mul_le_mul_of_nonneg_left (fullKernelOfEntries_entryNorm_le _ _ _ _ _ shift)
      (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative _ _) (pow_nonneg (annularFrequency_pos shift).le moment)))
    (phaseEulerKernelEntry_moments parameters radius rank kernel moment) |>.trans_eq
  unfold fullKernelMoment
  rw [← tsum_mul_left]
  apply tsum_congr
  intro shift
  rw [pow_add]
  ring

theorem phaseEulerKernel_entry_actual {source target : ℕ} (parameters : PhaseParameters) (radius : RadialPoint)
    (rank : ℕ) (kernel : RadialKernel parameters radius source target) (shift input : ℤ × ℤ) :
    radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2 radius.val •
      (phaseEulerKernel parameters radius rank kernel).entry shift input =
    eulerIteratedDerivative rank
      (radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2) radius.val • kernel.entry shift input := by
  have positive : 0 < radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2 radius.val := Real.exp_pos _
  ext vector coordinate
  change (radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2 radius.val : ℂ) *
    ((phaseEulerMultiplier parameters rank radius shift input : ℂ) * (kernel.entry shift input vector coordinate)) =
    (eulerIteratedDerivative rank (radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2) radius.val : ℂ) *
      (kernel.entry shift input vector coordinate)
  rw [phaseEulerMultiplier,Complex.ofReal_div]
  field_simp [Complex.ofReal_ne_zero.mpr positive.ne']

end Grad.OriginalCartesianTameEstimate
