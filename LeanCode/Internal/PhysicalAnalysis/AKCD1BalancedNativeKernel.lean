import AKBZ31OriginalPhysicalFrameConsumer
import AKBY6ActualOriginalSourceAllMoments

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularKernelL2

def nativeBalance (grade : ℕ) (shift input : ℤ × ℤ) : ℝ :=
  annularFrequency (input + shift).1 (input + shift).2 ^ grade /
    (annularFrequency input.1 input.2 ^ grade + annularFrequency shift.1 shift.2 ^ grade)

theorem nativeBalance_nonnegative (grade : ℕ) (shift input : ℤ × ℤ) :
    0 ≤ nativeBalance grade shift input := by
  unfold nativeBalance
  exact div_nonneg (pow_nonneg (annularFrequency_pos (input+shift)).le _)
    (add_nonneg (pow_nonneg (annularFrequency_pos input).le _) (pow_nonneg (annularFrequency_pos shift).le _))

theorem nativeBalance_bound (grade : ℕ) (shift input : ℤ × ℤ) :
    nativeBalance grade shift input ≤ 2 ^ grade := by
  have denominator : 0 < annularFrequency input.1 input.2 ^ grade + annularFrequency shift.1 shift.2 ^ grade :=
    add_pos (pow_pos (annularFrequency_pos input) _) (pow_pos (annularFrequency_pos shift) _)
  rw [nativeBalance, div_le_iff₀ denominator]
  simpa only [add_sub_cancel_right] using productFrequency_power grade (input+shift) shift

def nativeBalancedEntry {input output : ℕ} {parameters : PhaseParameters}
    (kernel : FullTwoFrequencyKernel parameters input output) (grade extra : ℕ) (shift cell : ℤ × ℤ) :
    ComplexEuclidean input →L[ℂ] ComplexEuclidean output :=
  ((annularFrequency shift.1 shift.2 ^ extra * nativeBalance grade shift cell : ℝ) : ℂ) • kernel.entry shift cell

theorem nativeBalancedEntry_bound {input output : ℕ} {parameters : PhaseParameters}
    (kernel : FullTwoFrequencyKernel parameters input output) (grade extra : ℕ) (shift cell : ℤ × ℤ) :
    ‖nativeBalancedEntry kernel grade extra shift cell‖ ≤
      2 ^ grade * annularFrequency shift.1 shift.2 ^ extra * kernel.entryNorm shift := by
  apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
  rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (pow_nonneg (annularFrequency_pos shift).le _) (nativeBalance_nonnegative _ _ _))]
  exact (mul_le_mul (mul_le_mul_of_nonneg_left (nativeBalance_bound grade shift cell)
      (pow_nonneg (annularFrequency_pos shift).le _)) (kernel.entry_le shift cell) (norm_nonneg _)
      (mul_nonneg (pow_nonneg (annularFrequency_pos shift).le _) (by positivity))).trans_eq (by ring)

theorem nativeBalancedEntry_moments {input output : ℕ} {parameters : PhaseParameters}
    (kernel : FullTwoFrequencyKernel parameters input output) (grade extra moment : ℕ) :
    Summable (fun shift : ℤ × ℤ => boundaryCoefficientPhaseCost parameters shift *
      annularFrequency shift.1 shift.2 ^ moment *
        (2 ^ grade * annularFrequency shift.1 shift.2 ^ extra * kernel.entryNorm shift)) := by
  apply ((kernel.moments (moment+extra)).mul_left ((2:ℝ)^grade)).congr
  intro shift
  rw [pow_add]
  ring

def nativeBalancedKernel {input output : ℕ} {parameters : PhaseParameters}
    (kernel : FullTwoFrequencyKernel parameters input output) (grade extra : ℕ) :
    FullTwoFrequencyKernel parameters input output :=
  fullKernelOfEntries parameters (nativeBalancedEntry kernel grade extra)
    (fun shift => 2 ^ grade * annularFrequency shift.1 shift.2 ^ extra * kernel.entryNorm shift)
    (nativeBalancedEntry_bound kernel grade extra) (nativeBalancedEntry_moments kernel grade extra)

theorem nativeBalancedKernel_moment {input output : ℕ} {parameters : PhaseParameters}
    (kernel : FullTwoFrequencyKernel parameters input output) (grade extra moment : ℕ) :
    fullKernelMoment parameters moment (nativeBalancedKernel kernel grade extra) ≤
      2 ^ grade * fullKernelMoment parameters (moment+extra) kernel := by
  apply ((nativeBalancedKernel kernel grade extra).moments moment).tsum_le_tsum
    (fun shift => mul_le_mul_of_nonneg_left (fullKernelOfEntries_entryNorm_le _ _ _ _ _ shift)
      (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative _ _) (pow_nonneg (annularFrequency_pos shift).le _)))
    (nativeBalancedEntry_moments kernel grade extra moment) |>.trans_eq
  unfold fullKernelMoment
  rw [← tsum_mul_left]
  apply tsum_congr
  intro shift
  rw [pow_add]
  ring

end Grad.OriginalCartesianTameEstimate
