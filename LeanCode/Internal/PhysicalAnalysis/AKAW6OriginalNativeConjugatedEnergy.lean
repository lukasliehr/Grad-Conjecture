import AKAW5SameConjugatedCurve

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.ActualNativeCellMoments
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.PhaseAlgebra
open Grad.ActualPuncturedReconstruction Grad.PuncturedRetainedEnergy Grad.AnnularIncomingIntegrability

theorem phaseWeighted_lowPhysicalCoefficient_bound {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (row : DivisionRow dimension lower)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    ‖(Real.exp (radialPhase parameters radius mode.2) : ℂ) •
      lowRhoPhysicalCoefficient parameters lower positive row radius mode‖ ≤ ‖row mode radius‖ := by
  have radiusPositive := positive.trans_le inside.1
  have cancel : Real.exp (radialPhase parameters radius mode.2) *
      (lowRhoPhysicalWeight parameters lower positive radius mode)⁻¹ = radius ^ (7/4 : ℝ) := by
    rw [lowRhoPhysicalWeight,mul_inv_rev,← mul_assoc,mul_inv_cancel₀ (Real.exp_pos _).ne',one_mul]
    change ((max lower radius) ^ (-(7/4 : ℝ)))⁻¹ = _
    rw [max_eq_right inside.1,Real.rpow_neg radiusPositive.le,inv_inv]
  rw [lowRhoPhysicalCoefficient,norm_smul,norm_smul,norm_inv,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_of_nonneg (lowRhoPhysicalWeight_pos parameters lower positive radius mode).le,
    ← mul_assoc,cancel]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.rpow_le_one radiusPositive.le inside.2 (by norm_num))

variable {dimension : ℕ} (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow dimension (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      Grad.AnnularRestriction.originalBulkRestriction dimension (lower second) (lower first) (decreasing ordered) (rows second)=rows first)
include bounded compatible

theorem sameConjugatedCurve_nativeSquare (index : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc (lower index) 1),
      ENNReal.ofReal (‖gluedWeightedFamilyCurve parameters lower positive cofinal rows curves 0 radius‖ ^ 2) ≤
        physicalBulkSquare dimension (lower index) (rows index) radius := by
  filter_upwards [(curves index).same 0,ae_restrict_mem measurableSet_Icc] with radius same inside
  rw [gluedWeightedFamilyCurve_same parameters lower positive bounded cofinal decreasing rows curves compatible 0 index radius inside]
  have square : ‖(curves index).curve 0 radius‖ ^ 2 = ∑' mode, ‖(curves index).curve 0 radius mode‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using
      (lp.norm_rpow_eq_tsum (p := 2) (by norm_num) ((curves index).curve 0 radius))
  rw [square,ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (lp_summable_sq ((curves index).curve 0 radius))]
  apply ENNReal.tsum_le_tsum
  intro mode
  apply ENNReal.ofReal_le_ofReal
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
  rw [same mode,pow_zero,one_smul]
  exact phaseWeighted_lowPhysicalCoefficient_bound parameters (lower index) (positive index) (rows index) radius inside mode

/-- Exact original-width conjugation is controlled on the full punctured disk
by the original common-storage native row energy. -/
theorem sameConjugatedCurve_globalEnergy (constant : ℝ) (estimate : ∀ index, ‖rows index‖ ≤ constant) :
    (∫⁻ radius in Ioc (0 : ℝ) 1,
      ENNReal.ofReal (‖gluedWeightedFamilyCurve parameters lower positive cofinal rows curves 0 radius‖ ^ 2)) ≤
        ENNReal.ofReal (constant ^ 2) := by
  have bound := cofinalEnergy_bound 1 lower positive decreasing cofinal
    (fun radius => ENNReal.ofReal (‖gluedWeightedFamilyCurve parameters lower positive cofinal rows curves 0 radius‖ ^ 2))
    0 (ENNReal.ofReal (constant ^ 2)) (fun index => ?_)
  · simpa only [add_zero] using bound
  · rw [add_zero]
    calc
      _ ≤ ∫⁻ radius in Icc (lower index) 1, physicalBulkSquare dimension (lower index) (rows index) radius :=
        lintegral_mono_ae (sameConjugatedCurve_nativeSquare parameters lower positive bounded cofinal decreasing rows curves compatible index)
      _ = _ := physicalBulkSquare_integral dimension _ _
      _ ≤ _ := ENNReal.ofReal_le_ofReal
        ((sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (estimate index))).mpr (estimate index))

end Grad.ActualNativeCellMoments
