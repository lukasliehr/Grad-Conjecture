import AKO3ActualHighIncomingRepresentatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped ENNReal BigOperators
namespace Grad.AnnularIncomingIntegrability
open Grad.ClosedJets Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.AnnularReconstruction Grad.AnnularRestriction
open Grad.AnnularGrades Grad.AnnularTiltedReference Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.WeightedTrace

private theorem highCoefficientLogBound (radius frequency square : ℝ) (positive : 0 < radius)
    (frequencyOne : 1 ≤ frequency) (squareNonnegative : 0 ≤ square) :
    radius⁻¹ * (frequency * ((1 / Real.sqrt radius) ^ 2 * square)) ≤
      frequency ^ 2 * ((2 / radius) ^ 2 * square) := by
  have frequencyBound : frequency ≤ 4 * frequency ^ 2 := by nlinarith
  have scaled := mul_le_mul_of_nonneg_right frequencyBound (mul_nonneg (sq_nonneg radius⁻¹) squareNonnegative)
  rw [div_pow,one_pow,Real.sq_sqrt positive.le]
  simp only [div_eq_mul_inv,mul_pow] at *
  nlinarith only [scaled]

variable (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)

/-- Actual high incoming squared norm through the SAME decoded H1 sections. -/
def highIncomingSquare (field : annularEnergySpace lower length positive) (radius : ℝ) : ℝ≥0∞ :=
  ∑' mode : HighAnnularMode, ENNReal.ofReal (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 *
    ‖highIncomingRepresentative lower length positive bounded field mode radius‖ ^ 2)

/-- Inserted grade one supplies the actual high logarithmic incoming energy.
The bound is independent of the removed inner radius. -/
theorem highIncomingSquare_log_bound (field weighted : annularEnergySpace lower length positive)
    (same : ∀ mode : HighAnnularMode, weighted.val mode =
      (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 : ℂ) • field.val mode) :
    (∫⁻ radius, ENNReal.ofReal radius⁻¹ * highIncomingSquare lower length positive bounded field radius
      ∂volume.restrict (Icc lower 1)) ≤ ENNReal.ofReal (‖weighted‖ ^ 2) := by
  let radial := annularEnergyRadial lower length positive (bEnergyDecode lower length positive weighted)
  have pointwise : (∫⁻ radius, ENNReal.ofReal radius⁻¹ * highIncomingSquare lower length positive bounded field radius
      ∂volume.restrict (Icc lower 1)) ≤ ENNReal.ofReal (‖radial‖ ^ 2) := by
    rw [← lp_lintegral_tsum_sq lower radial]
    apply lintegral_mono_ae
    filter_upwards [ae_all_iff.mpr (highIncomingRepresentative_stored lower length positive bounded field),
      ae_all_iff.mpr (highIncomingRadial_stored lower length positive field),
      ae_all_iff.mpr (fun mode : HighAnnularMode => Lp.coeFn_smul
        (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 : ℂ)
        (annularEnergyRadial lower length positive (bEnergyDecode lower length positive field) mode)),
      ae_restrict_mem measurableSet_Icc] with radius representative radialLaw scalarLaw inside
    have radiusPositive := positive.trans_le inside.1
    change ENNReal.ofReal radius⁻¹ * (∑' mode : HighAnnularMode, ENNReal.ofReal _) ≤ _
    rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro mode
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr radiusPositive.le)]
    apply ENNReal.ofReal_le_ofReal
    have graded := congrArg (fun value : CollarL2 (ComplexEuclidean 1) lower => value radius)
      (insertedHigh_radial_mode lower length positive field weighted same mode)
    rw [scalarLaw mode] at graded
    simp only [Pi.smul_apply] at graded
    change _ ≤ ‖annularEnergyRadial lower length positive (bEnergyDecode lower length positive weighted) mode radius‖ ^ 2
    rw [representative mode,graded,radialLaw mode]
    simp only [reciprocalRadialWeight,annularRadialCurve,ContinuousMap.coe_mk,max_eq_right inside.1,
      norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
    exact highCoefficientLogBound radius _ _ radiusPositive (annularFrequency_one_le _ _) (sq_nonneg _)
  have decoded : ‖bEnergyDecode lower length positive weighted‖ ≤ ‖weighted‖ := by
    exact (annularEnergyDiagonal_bound lower length positive (fun mode => Real.sqrt (highMultiplier mode.val.1))
      1 (by norm_num) bEnergyDecode_bound weighted).trans_eq (one_mul _)
  have radialBound := annularEnergyRadial_bound lower length positive (bEnergyDecode lower length positive weighted)
  have bound : ‖radial‖ ≤ ‖weighted‖ := by dsimp only [radial]; nlinarith [norm_nonneg weighted]
  exact pointwise.trans (ENNReal.ofReal_le_ofReal ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr bound))

end Grad.AnnularIncomingIntegrability
