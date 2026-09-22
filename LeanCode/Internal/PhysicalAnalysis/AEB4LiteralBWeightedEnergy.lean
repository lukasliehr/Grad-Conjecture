import AEB3CoerciveTiltedReferenceForm
import AAT2EnergyDiagonal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open MeasureTheory
open scoped Topology Interval BigOperators
namespace Grad.AnnularTiltedReference
open Grad.ClosedJets Grad.AnnularVariational Grad.AnnularGrades Grad.CircularHighWeak
open Grad.ActualReferenceAssembly

def bEnergyWeight (mode : HighAnnularMode) : ℝ := (Real.sqrt (highMultiplier mode.val.1))⁻¹

theorem highMultiplier_positive (mode : HighAnnularMode) : 0 < highMultiplier mode.val.1 :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 5 / 9)
    (highMultiplier_bounds mode.val.1 (highMode_not_low mode.val.1 mode.property)).1

theorem bEnergyWeight_positive (mode : HighAnnularMode) : 0 < bEnergyWeight mode :=
  inv_pos.mpr (Real.sqrt_pos.mpr (highMultiplier_positive mode))

theorem bEnergyWeight_square (mode : HighAnnularMode) :
    bEnergyWeight mode ^ 2 = (highMultiplier mode.val.1)⁻¹ := by
  rw [bEnergyWeight, inv_pow, Real.sq_sqrt (highMultiplier_positive mode).le]

theorem bEnergyDecode_bound (mode : HighAnnularMode) :
    |Real.sqrt (highMultiplier mode.val.1)| ≤ 1 := by
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (Real.sqrt_le_iff).mpr ⟨by norm_num,
    by simpa using (highMultiplier_bounds mode.val.1 (highMode_not_low mode.val.1 mode.property)).2⟩

theorem bEnergyWeight_bound (mode : HighAnnularMode) : |bEnergyWeight mode| ≤ 2 := by
  rw [abs_of_pos (bEnergyWeight_positive mode)]
  have rootPositive := Real.sqrt_pos.mpr (highMultiplier_positive mode)
  have rootSquare := Real.sq_sqrt (highMultiplier_positive mode).le
  have lowerBound := (highMultiplier_bounds mode.val.1 (highMode_not_low mode.val.1 mode.property)).1
  change (Real.sqrt (highMultiplier mode.val.1))⁻¹ ≤ 2
  rw [inv_eq_one_div]
  apply (div_le_iff₀ rootPositive).mpr
  nlinarith [sq_nonneg (Real.sqrt (highMultiplier mode.val.1) - 1 / 2)]

/-- Physical w is sqrt(b_m) times the stored AAG energy coordinates. -/
def bEnergyDecode (lower length : ℝ) (positive : 0 < lower) :
    annularEnergySpace lower length positive →L[ℂ] annularEnergySpace lower length positive :=
  annularEnergyDiagonal lower length positive (fun mode => Real.sqrt (highMultiplier mode.val.1))
    1 (by norm_num) bEnergyDecode_bound

def bEnergyNormalize (lower length : ℝ) (positive : 0 < lower) :
    annularEnergySpace lower length positive →L[ℂ] annularEnergySpace lower length positive :=
  annularEnergyDiagonal lower length positive bEnergyWeight 2 (by norm_num) bEnergyWeight_bound

theorem bEnergyDecode_normalize (lower length : ℝ) (positive : 0 < lower)
    (field : annularEnergySpace lower length positive) :
    bEnergyDecode lower length positive (bEnergyNormalize lower length positive field) = field := by
  apply Subtype.ext
  apply lp.ext
  funext mode
  simp only [bEnergyDecode, bEnergyNormalize, annularEnergyDiagonal_apply, bEnergyWeight,
    smul_smul, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (Real.sqrt_pos.mpr (highMultiplier_positive mode)).ne', Complex.ofReal_one, one_smul]

theorem bEnergyNormalize_decode (lower length : ℝ) (positive : 0 < lower)
    (field : annularEnergySpace lower length positive) :
    bEnergyNormalize lower length positive (bEnergyDecode lower length positive field) = field := by
  apply Subtype.ext
  apply lp.ext
  funext mode
  simp only [bEnergyDecode, bEnergyNormalize, annularEnergyDiagonal_apply, bEnergyWeight,
    smul_smul, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr (highMultiplier_positive mode)).ne', Complex.ofReal_one, one_smul]

/-- The same closed Hilbert carrier, with the literal BF energy normalization. -/
def bEnergyCore (lower length : ℝ) (positive : 0 < lower) :
    (HighAnnularMode →₀ complexSmoothRadialCore 1) →ₗ[ℂ] annularEnergySpace lower length positive :=
  (annularEnergyCoreInto lower length positive).comp (finiteRealDiagonal bEnergyWeight)

theorem bEnergyCore_denseRange (lower length : ℝ) (positive : 0 < lower) :
    DenseRange (bEnergyCore lower length positive) := by
  apply (annularEnergyCoreInto_denseRange lower length positive).mono
  rintro _ ⟨core, rfl⟩
  refine ⟨finiteRealDiagonal (fun mode => (bEnergyWeight mode)⁻¹) core, ?_⟩
  unfold bEnergyCore
  rw [LinearMap.comp_apply]
  congr 1
  apply Finsupp.ext
  intro mode
  rw [finiteRealDiagonal_apply, finiteRealDiagonal_apply, smul_smul, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (bEnergyWeight_positive mode).ne', Complex.ofReal_one, one_smul]

theorem bEnergyCore_decode (lower length : ℝ) (positive : 0 < lower)
    (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    bEnergyDecode lower length positive (bEnergyCore lower length positive core) =
      annularEnergyCoreInto lower length positive core := by
  unfold bEnergyCore bEnergyDecode
  rw [LinearMap.comp_apply, annularEnergyDiagonal_core]
  congr 1
  apply Finsupp.ext
  intro mode
  rw [finiteRealDiagonal_apply, finiteRealDiagonal_apply, smul_smul, ← Complex.ofReal_mul]
  simp only [bEnergyWeight, mul_inv_cancel₀ (Real.sqrt_pos.mpr (highMultiplier_positive mode)).ne',
    Complex.ofReal_one, one_smul]

/-- Exactly E_B squared, including +2 b_m^-1 times the actual outer value. -/
theorem bEnergyCore_norm_sq (lower length : ℝ) (positive : 0 < lower) (collar : lower ≤ 1)
    (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    ‖bEnergyCore lower length positive core‖ ^ 2 =
      ∑' mode : HighAnnularMode, (highMultiplier mode.val.1)⁻¹ *
        ((∫ radius in lower..1, radius * (‖(core mode).val.2 radius‖ ^ 2 +
          annularPotential length radius mode.val.1 mode.val.2 * ‖(core mode).val.1 radius‖ ^ 2)) +
          2 * ‖(core mode).val.1 1‖ ^ 2) := by
  have formula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (bEnergyCore lower length positive core).val
  norm_num at formula
  change ‖(bEnergyCore lower length positive core).val‖ ^ 2 = _
  rw [formula]
  apply tsum_congr
  intro mode
  change ‖finiteAnnularEnergyCore lower length positive (finiteRealDiagonal bEnergyWeight core) mode‖ ^ 2 = _
  rw [finiteAnnularEnergyCore_apply, finiteRealDiagonal_apply, map_smul,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    bEnergyWeight_square, annularModeEnergyCore_norm_sq lower length positive collar]

end Grad.AnnularTiltedReference
