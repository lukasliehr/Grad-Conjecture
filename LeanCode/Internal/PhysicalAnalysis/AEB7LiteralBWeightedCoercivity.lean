import AEB6TiltFormBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open MeasureTheory
open scoped Topology Interval BigOperators
namespace Grad.AnnularTiltedReference
open Grad.ClosedJets Grad.CartesianState Grad.AnnularVariational Grad.AnnularGrades Grad.CircularHighWeak

/-- The completed norm is literally the b_m^-1 sum of decoded energy coordinates. -/
theorem bEnergyDecode_norm_sq (lower length : ℝ) (positive : 0 < lower)
    (field : annularEnergySpace lower length positive) :
    ‖field‖ ^ 2 = ∑' mode : HighAnnularMode, (highMultiplier mode.val.1)⁻¹ *
      ‖(bEnergyDecode lower length positive field).val mode‖ ^ 2 := by
  have formula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field.val
  norm_num at formula
  change ‖field.val‖ ^ 2 = _
  rw [formula]
  apply tsum_congr
  intro mode
  rw [bEnergyDecode, annularEnergyDiagonal_apply, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt (highMultiplier_positive mode).le,
    ← mul_assoc, inv_mul_cancel₀ (highMultiplier_positive mode).ne', one_mul]

theorem bEnergyCore_innerZero (lower length : ℝ) (positive : 0 < lower)
    (collar : lower < 1) (lengthPositive : 0 < length)
    (core : HighAnnularMode →₀ complexSmoothRadialCore 1)
    (innerZero : ∀ mode, (core mode).val.1 lower = 0) :
    bEnergyCore lower length positive core ∈ annularInnerZero lower length positive collar lengthPositive := by
  change annularEnergyTrace lower length positive collar lengthPositive 0
    (annularEnergyCoreInto lower length positive (finiteRealDiagonal bEnergyWeight core)) = 0
  rw [annularEnergyTrace_core]
  apply lp.ext
  funext mode
  rw [finiteAnnularTraceCore_apply, finiteRealDiagonal_apply]
  change (Real.sqrt (annularFrequency mode.val.1 mode.val.2) : ℂ) •
    ((bEnergyWeight mode : ℂ) • (core mode).val.1 lower) = 0
  rw [innerZero, smul_zero, smul_zero]

section Form
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- Literal BF8 on the actual smooth core, including the original weighted
outer term. The phase uses every original input cell frequency. -/
theorem bEnergyCore_tilt_diagonal (collar : lower ≤ 1)
    (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    (annularTiltFormValue parameters lower length positive lengthPositive widthHalf widthLength
      (bEnergyCore lower length positive core) (bEnergyCore lower length positive core)).re =
      (∑' mode : HighAnnularMode, (highMultiplier mode.val.1)⁻¹ *
        ((∫ radius in lower..1, radius * (‖(core mode).val.2 radius‖ ^ 2 +
          annularPotential length radius mode.val.1 mode.val.2 * ‖(core mode).val.1 radius‖ ^ 2)) +
          2 * ‖(core mode).val.1 1‖ ^ 2)) -
      ∑' mode : HighAnnularMode, (highMultiplier mode.val.1)⁻¹ *
        ∫ radius in lower..1, radius *
          (annularPhaseSlope parameters mode.val.2 radius - annularTiltExponent / radius) ^ 2 *
          ‖(core mode).val.1 radius‖ ^ 2 := by
  rw [← annularTiltForm_literal, annularTiltForm_diagonal,
    bEnergyCore_norm_sq lower length positive collar,
    annularTiltEnergyPhase_bCore_norm_sq parameters lower length positive lengthPositive widthHalf widthLength collar]

/-- BF10 is coercivity in the completed literal E_B norm; no b weight or
outer coefficient is omitted by the stored-coordinate normalization. -/
theorem bEnergy_tilt_coercivity (field : annularEnergySpace lower length positive) :
    (1 / 16 : ℝ) *
      (∑' mode : HighAnnularMode, (highMultiplier mode.val.1)⁻¹ *
        ‖(bEnergyDecode lower length positive field).val mode‖ ^ 2) ≤
      (annularTiltFormValue parameters lower length positive lengthPositive widthHalf widthLength field field).re := by
  rw [← bEnergyDecode_norm_sq, ← annularTiltForm_literal]
  exact annularTiltForm_coercive_bound parameters lower length positive lengthPositive widthHalf widthLength field

end Form
end Grad.AnnularTiltedReference
