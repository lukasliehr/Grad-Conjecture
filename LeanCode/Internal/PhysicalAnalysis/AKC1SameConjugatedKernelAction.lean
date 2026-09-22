import AJI18HilbertFrequencyOperators
import AJH16OriginalSevenSlotSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open Set
open scoped Topology BigOperators
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.BoundaryLift Grad.AnnularKernelL2
open Grad.AnnularReconstruction Grad.AnnularSmoothCore

def frequencyReserveSymbol (reserve : ℕ) (mode : ℤ × ℤ) : ℂ :=
  ((annularFrequency mode.1 mode.2 : ℂ) ^ reserve)⁻¹

theorem frequencyReserveSymbol_bound (reserve : ℕ) (mode : ℤ × ℤ) :
    ‖frequencyReserveSymbol reserve mode‖ ≤ 1 := by
  have positive := Grad.SourceBoundaryTrace.annularFrequency_pos mode
  have one : 1 ≤ annularFrequency mode.1 mode.2 := by
    change 1 ≤ 1 + |(mode.1 : ℝ)| + |(mode.2 : ℝ)|
    linarith [abs_nonneg (mode.1 : ℝ), abs_nonneg (mode.2 : ℝ)]
  rw [frequencyReserveSymbol, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg positive.le]
  exact (inv_le_one₀ (pow_pos positive reserve)).2 (one_le_pow₀ one)

def hilbertReserve (parameters : PhaseParameters) (dimension reserve : ℕ) :
    CellL2 dimension →L[ℂ] CellL2 dimension :=
  boundedHilbertMultiplier parameters dimension (frequencyReserveSymbol reserve) 1 zero_le_one
    (frequencyReserveSymbol_bound reserve)

theorem hilbertReserve_apply (parameters : PhaseParameters) (dimension reserve : ℕ)
    (field : CellL2 dimension) (mode : ℤ × ℤ) :
    hilbertReserve parameters dimension reserve field mode = frequencyReserveSymbol reserve mode • field mode := rfl

theorem hilbertReserve_norm_le (parameters : PhaseParameters) (dimension reserve : ℕ) :
    ‖hilbertReserve parameters dimension reserve‖ ≤ 1 :=
  coefficientOperator_norm_le parameters 0 (Equiv.refl _) _ zero_le_one _

theorem hilbertReserve_same (parameters : PhaseParameters) (dimension reserve : ℕ)
    (higher lower : CellL2 dimension)
    (same : ∀ mode, higher mode = (annularFrequency mode.1 mode.2 : ℂ) ^ reserve • lower mode) :
    hilbertReserve parameters dimension reserve higher = lower := by
  apply lp.ext
  funext mode
  rw [hilbertReserve_apply, same mode, frequencyReserveSymbol, inv_smul_smul₀]
  exact pow_ne_zero reserve (by exact_mod_cast (Grad.SourceBoundaryTrace.annularFrequency_pos mode).ne')

/-- The accepted original-width bulk action, with only an explicit polynomial
input reserve. Its Fourier phase and kernel are unchanged. -/
def conjugatedKernelAction {source target : ℕ} (parameters : PhaseParameters)
    (grade reserve : ℕ) (radius : RadialPoint) (kernel : RadialKernel parameters radius source target) :
    CellL2 source →L[ℂ] CellL2 target :=
  (bulkKernelAction parameters grade radius kernel).comp (hilbertReserve parameters source reserve)

theorem conjugatedKernelAction_coefficient {source target : ℕ} (parameters : PhaseParameters)
    (grade reserve : ℕ) (radius : RadialPoint) (kernel : RadialKernel parameters radius source target)
    (field : CellL2 source) (mode : ℤ × ℤ) :
    HasSum (fun shift => ((bulkWeightRatio parameters grade radius.val shift mode : ℂ) *
      frequencyReserveSymbol reserve (twoFrequencyTranslation shift mode)) •
        kernel.entry shift (twoFrequencyTranslation shift mode) (field (twoFrequencyTranslation shift mode)))
      (conjugatedKernelAction parameters grade reserve radius kernel field mode) := by
  apply (bulkKernelAction_coordinate parameters grade radius kernel (hilbertReserve parameters source reserve field) mode).congr_fun
  intro shift
  rw [hilbertReserve_apply, map_smul, smul_smul]

theorem conjugatedKernelAction_norm_le {source target : ℕ} (parameters : PhaseParameters)
    (grade reserve : ℕ) (radius : RadialPoint) (kernel : RadialKernel parameters radius source target) :
    ‖conjugatedKernelAction parameters grade reserve radius kernel‖ ≤
      fullKernelMoment (radialKernelParameters parameters radius) grade kernel := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (bulkKernelAction_norm_le parameters grade radius kernel)
      (hilbertReserve_norm_le parameters source reserve) (norm_nonneg _) (fullKernelMoment_nonnegative _ _ _)).trans_eq (mul_one _))

theorem conjugatedKernelAction_same {source target : ℕ} (parameters : PhaseParameters)
    (grade reserve : ℕ) (radius : RadialPoint) (kernel : RadialKernel parameters radius source target)
    (higher lower : CellL2 source)
    (same : ∀ mode, higher mode = (annularFrequency mode.1 mode.2 : ℂ) ^ reserve • lower mode) :
    conjugatedKernelAction parameters grade reserve radius kernel higher = bulkKernelAction parameters grade radius kernel lower := by
  change bulkKernelAction parameters grade radius kernel (hilbertReserve parameters source reserve higher) = _
  exact congrArg (bulkKernelAction parameters grade radius kernel) (hilbertReserve_same parameters source reserve higher lower same)

def radialConjugatedAction {source target : ℕ} (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius source target)
    (grade reserve : ℕ) (radius : ℝ) : CellL2 source →L[ℂ] CellL2 target :=
  conjugatedKernelAction parameters grade reserve (collarRadius lower positive bounded radius)
    (kernel (collarRadius lower positive bounded radius))

end Grad.AnnularWeightedSmoothness
