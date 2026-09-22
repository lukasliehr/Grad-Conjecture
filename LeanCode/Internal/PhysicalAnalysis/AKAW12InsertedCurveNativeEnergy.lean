import AKAW8SameNativeCellCarrier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.ActualNativeCellMoments
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.PhaseAlgebra
open Grad.ActualPuncturedReconstruction Grad.PuncturedRetainedEnergy Grad.AnnularIncomingIntegrability

variable {dimension : ℕ} (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (row : DivisionRow dimension lower) (curves : SmoothLowPhysicalRow parameters lower positive row)
    (grade : ℕ) (weighted : DivisionRow dimension lower)
    (same : ∀ mode : ℤ × ℤ, weighted mode = ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) • row mode)
include same

/-- A literal insertion in the existing native row supplies the SAME weighted
curve's energy. The phase and radial storage cancel exactly once. -/
theorem insertedCurve_nativeSquare :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ENNReal.ofReal (‖curves.curve grade radius‖ ^ 2) ≤
      physicalBulkSquare dimension lower weighted radius := by
  have scaled (mode : ℤ × ℤ) := Lp.coeFn_smul ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) (row mode)
  filter_upwards [curves.same grade,ae_all_iff.mpr scaled,ae_restrict_mem measurableSet_Icc] with radius actual stored inside
  have pointBound (mode : ℤ × ℤ) : ‖curves.curve grade radius mode‖ ≤ ‖weighted mode radius‖ := by
    have equal : curves.curve grade radius mode = (Real.exp (radialPhase parameters radius mode.2) : ℂ) •
        lowRhoPhysicalCoefficient parameters lower positive weighted radius mode := by
      rw [actual mode,lowRhoPhysicalCoefficient,lowRhoPhysicalCoefficient,same mode,stored mode]
      simp only [Complex.ofReal_pow,Pi.smul_apply]
      exact (smul_comm _ _ _).trans (congrArg (fun value => (Real.exp (radialPhase parameters radius mode.2) : ℂ) • value)
        (smul_comm _ _ _))
    rw [equal]
    exact phaseWeighted_lowPhysicalCoefficient_bound parameters lower positive weighted radius inside mode
  have square : ‖curves.curve grade radius‖ ^ 2 = ∑' mode, ‖curves.curve grade radius mode‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using
      (lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (curves.curve grade radius))
  rw [square,ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (lp_summable_sq (curves.curve grade radius))]
  exact ENNReal.tsum_le_tsum (fun mode => ENNReal.ofReal_le_ofReal
    ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (pointBound mode)))

theorem insertedCurve_collarEnergy :
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal (‖curves.curve grade radius‖ ^ 2)) ≤ ENNReal.ofReal (‖weighted‖ ^ 2) :=
  (lintegral_mono_ae (insertedCurve_nativeSquare parameters lower positive row curves grade weighted same)).trans_eq
    (physicalBulkSquare_integral dimension lower weighted)

end Grad.ActualNativeCellMoments
