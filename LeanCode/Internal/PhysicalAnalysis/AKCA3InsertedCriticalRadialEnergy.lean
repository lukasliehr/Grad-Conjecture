import AKCA2OriginalCriticalRadialEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators
namespace Grad.OriginalCoreRealization
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.PhaseAlgebra
open Grad.ActualPuncturedReconstruction Grad.PuncturedRetainedEnergy Grad.AnnularIncomingIntegrability

 theorem phaseWeighted_criticalRadius_contraction {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (row : DivisionRow dimension lower)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    ‖radius ^ (-(3 / 2 : ℝ)) • ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
      lowRhoPhysicalCoefficient parameters lower positive row radius mode)‖ ≤ ‖row mode radius‖ := by
  have radiusPositive := positive.trans_le inside.1
  have cancel : Real.exp (radialPhase parameters radius mode.2) *
      (lowRhoPhysicalWeight parameters lower positive radius mode)⁻¹ = radius ^ (7/4 : ℝ) := by
    rw [lowRhoPhysicalWeight,mul_inv_rev,← mul_assoc,mul_inv_cancel₀ (Real.exp_pos _).ne',one_mul]
    change ((max lower radius) ^ (-(7/4 : ℝ)))⁻¹ = _
    rw [max_eq_right inside.1,Real.rpow_neg radiusPositive.le,inv_inv]
  rw [lowRhoPhysicalCoefficient,norm_smul,norm_smul,norm_smul,norm_inv,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg radiusPositive.le _),
    Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_of_nonneg (lowRhoPhysicalWeight_pos parameters lower positive radius mode).le]
  have power : radius ^ (-(3 / 2 : ℝ)) * radius ^ (7/4 : ℝ) = radius ^ (1/4 : ℝ) := by
    rw [← Real.rpow_add radiusPositive]
    norm_num
  calc
    _ = (radius ^ (-(3 / 2 : ℝ)) *
        (Real.exp (radialPhase parameters radius mode.2) * (lowRhoPhysicalWeight parameters lower positive radius mode)⁻¹)) * ‖row mode radius‖ := by ring
    _ = radius ^ (1/4 : ℝ) * ‖row mode radius‖ := by rw [cancel,power]
    _ ≤ _ := mul_le_of_le_one_left (norm_nonneg _) (Real.rpow_le_one radiusPositive.le inside.2 (by norm_num))

 theorem insertedCurve_criticalNativeSquare {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (row : DivisionRow dimension lower)
    (curves : SmoothLowPhysicalRow parameters lower positive row) (grade : ℕ)
    (weighted : DivisionRow dimension lower)
    (same : ∀ mode : ℤ × ℤ, weighted mode = ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) • row mode) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ENNReal.ofReal
      (‖radius ^ (-(3 / 2 : ℝ)) • curves.curve grade radius‖ ^ 2) ≤ physicalBulkSquare dimension lower weighted radius := by
  have scaled (mode : ℤ × ℤ) := Lp.coeFn_smul ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) (row mode)
  filter_upwards [curves.same grade,ae_all_iff.mpr scaled,ae_restrict_mem measurableSet_Icc] with radius actual stored inside
  have pointBound (mode : ℤ × ℤ) :
      ‖radius ^ (-(3 / 2 : ℝ)) • curves.curve grade radius mode‖ ≤ ‖weighted mode radius‖ := by
    have equal : curves.curve grade radius mode = (Real.exp (radialPhase parameters radius mode.2) : ℂ) •
        lowRhoPhysicalCoefficient parameters lower positive weighted radius mode := by
      rw [actual mode,lowRhoPhysicalCoefficient,lowRhoPhysicalCoefficient,same mode,stored mode]
      simp only [Complex.ofReal_pow,Pi.smul_apply]
      exact (smul_comm _ _ _).trans (congrArg (fun value => (Real.exp (radialPhase parameters radius mode.2) : ℂ) • value)
        (smul_comm _ _ _))
    rw [equal]
    exact phaseWeighted_criticalRadius_contraction parameters lower positive weighted radius inside mode
  have square : ‖radius ^ (-(3 / 2 : ℝ)) • curves.curve grade radius‖ ^ 2 =
      ∑' mode, ‖(radius ^ (-(3 / 2 : ℝ)) • curves.curve grade radius) mode‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using
      (lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (radius ^ (-(3 / 2 : ℝ)) • curves.curve grade radius))
  rw [square,ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (lp_summable_sq (radius ^ (-(3 / 2 : ℝ)) • curves.curve grade radius))]
  exact ENNReal.tsum_le_tsum (fun mode => ENNReal.ofReal_le_ofReal
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (pointBound mode)))

 theorem insertedCurve_criticalCollarEnergy {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (row : DivisionRow dimension lower)
    (curves : SmoothLowPhysicalRow parameters lower positive row) (grade : ℕ)
    (weighted : DivisionRow dimension lower)
    (same : ∀ mode : ℤ × ℤ, weighted mode = ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) • row mode) :
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖radius ^ (-(3 / 2 : ℝ)) • curves.curve grade radius‖ ^ 2)) ≤ ENNReal.ofReal (‖weighted‖ ^ 2) :=
  (lintegral_mono_ae (insertedCurve_criticalNativeSquare parameters lower positive row curves grade weighted same)).trans_eq
    (physicalBulkSquare_integral dimension lower weighted)

end Grad.OriginalCoreRealization
