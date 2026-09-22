import AKC8FourierMatrixPoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 250000
open Set
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.BoundaryLift Grad.AnnularKernelL2
open Grad.AnnularReconstruction Grad.AnnularKernelContinuity

theorem frequencyReserveSymbol_norm (reserve : ℕ) (mode : ℤ × ℤ) :
    ‖frequencyReserveSymbol reserve mode‖ = (annularFrequency mode.1 mode.2 ^ reserve)⁻¹ := by
  rw [frequencyReserveSymbol, norm_inv, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (annularFrequency_pos mode).le]

/-- Retain the original analytic envelope while extracting polynomial shift decay. -/
theorem weightedKernelEntry_decay {source target : ℕ} (parameters : PhaseParameters)
    (grade decay : ℕ) (radius : RadialPoint) (kernel : RadialKernel parameters radius source target)
    (constant : ℝ) (bounded : fullKernelMoment (radialKernelParameters parameters radius) (grade + decay) kernel ≤ constant)
    (shift mode : ℤ × ℤ) :
    bulkWeightRatio parameters grade radius.val shift mode *
      ‖kernel.entry shift (twoFrequencyTranslation shift mode)‖ ≤
        constant * (annularFrequency shift.1 shift.2 ^ decay)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos (annularFrequency_pos shift) decay)]
  have weighted := mul_le_mul (bulkWeightRatio_le parameters grade radius shift mode)
    (kernel.entry_le shift (twoFrequencyTranslation shift mode)) (norm_nonneg _)
    (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative _ _) (pow_nonneg (annularFrequency_pos shift).le _))
  have term := (fullKernelWeightedEnvelope_summable (radialKernelParameters parameters radius) (grade + decay) kernel).le_tsum shift
    (fun other _ => fullKernelWeightedEnvelope_nonnegative _ _ _ other)
  have product := mul_le_mul_of_nonneg_right weighted (pow_nonneg (annularFrequency_pos shift).le decay)
  apply product.trans
  apply le_trans _ (term.trans bounded)
  unfold fullKernelWeightedEnvelope
  rw [pow_add]
  ring_nf
  exact le_rfl

/-- One term of the exact original phase-conjugated matrix operator series. -/
def conjugatedMatrixPoint {source target : ℕ} (parameters : PhaseParameters)
    (grade reserve : ℕ) (radius : RadialPoint) (kernel : RadialKernel parameters radius source target)
    (index : (ℤ × ℤ) × (ℤ × ℤ)) : CellL2 source →L[ℂ] CellL2 target :=
  fourierMatrixPoint ((twoFrequencyTranslation index.1).symm index.2) index.2
    (((bulkWeightRatio parameters grade radius.val index.1 ((twoFrequencyTranslation index.1).symm index.2) : ℂ) *
      frequencyReserveSymbol reserve index.2) • kernel.entry index.1 index.2)

theorem conjugatedMatrixPoint_bound {source target : ℕ} (parameters : PhaseParameters)
    (grade reserve decay : ℕ) (radius : RadialPoint) (kernel : RadialKernel parameters radius source target)
    (constant : ℝ) (bounded : fullKernelMoment (radialKernelParameters parameters radius) (grade + decay) kernel ≤ constant)
    (index : (ℤ × ℤ) × (ℤ × ℤ)) :
    ‖conjugatedMatrixPoint parameters grade reserve radius kernel index‖ ≤
      constant * (annularFrequency index.1.1 index.1.2 ^ decay)⁻¹ *
        (annularFrequency index.2.1 index.2.2 ^ reserve)⁻¹ := by
  apply (fourierMatrixPoint_bound _ _ _).trans
  rw [norm_smul, norm_mul, frequencyReserveSymbol_norm, Complex.norm_real,
    Real.norm_of_nonneg (bulkWeightRatio_pos parameters grade radius.val _ _).le]
  have weighted := weightedKernelEntry_decay parameters grade decay radius kernel constant bounded index.1
    ((twoFrequencyTranslation index.1).symm index.2)
  simp only [Equiv.apply_symm_apply] at weighted
  calc
    _ = (bulkWeightRatio parameters grade radius.val index.1 ((twoFrequencyTranslation index.1).symm index.2) *
        ‖kernel.entry index.1 index.2‖) * (annularFrequency index.2.1 index.2.2 ^ reserve)⁻¹ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right weighted (inv_nonneg.mpr (pow_nonneg (annularFrequency_pos index.2).le _))

end Grad.AnnularWeightedSmoothness
