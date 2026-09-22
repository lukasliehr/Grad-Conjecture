import AAQ8CanonicalFluxSections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularFluxTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

def annularFluxTraceLinear (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (endpoint : Fin 2) :
    annularFluxWeakGraph lower positive →ₗ[ℂ] AnnularBoundary where
  toFun := annularFluxTraceFamily lower positive bounded endpoint
  map_add' first second := by
    apply lp.ext
    funext mode
    change annularFluxTraceCoefficient lower positive bounded endpoint (first + second) mode =
      annularFluxTraceCoefficient lower positive bounded endpoint first mode +
        annularFluxTraceCoefficient lower positive bounded endpoint second mode
    rw [annularFluxTraceCoefficient_section, annularFluxTraceCoefficient_section,
      annularFluxTraceCoefficient_section, annularFluxSection_add]
    exact smul_add _ _ _
  map_smul' scalar data := by
    apply lp.ext
    funext mode
    change annularFluxTraceCoefficient lower positive bounded endpoint (scalar • data) mode =
      scalar • annularFluxTraceCoefficient lower positive bounded endpoint data mode
    rw [annularFluxTraceCoefficient_section, annularFluxTraceCoefficient_section, annularFluxSection_smul]
    exact smul_comm (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2))⁻¹ scalar
      (annularFluxSection lower positive bounded data mode
        ⟨radialEndpointRadius lower endpoint, radialEndpointRadius_mem lower bounded.le endpoint⟩)

theorem annularFluxTraceLinear_bound (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (endpoint : Fin 2) (data : annularFluxWeakGraph lower positive) :
    ‖annularFluxTraceLinear lower positive bounded endpoint data‖ ≤ (2 * annularFluxTraceConstant lower) * ‖data‖ := by
  have estimate := annularFluxTraceFamily_bound lower positive bounded endpoint data
  have sumBound : ‖data.val.1‖ + ‖data.val.2‖ ≤ 2 * ‖data‖ := by
    have first := norm_fst_le data.val
    have second := norm_snd_le data.val
    change ‖data.val.1‖ + ‖data.val.2‖ ≤ 2 * ‖data.val‖
    linarith
  exact estimate.trans ((mul_le_mul_of_nonneg_left sumBound (annularFluxTraceConstant_nonnegative lower)).trans_eq (by ring))

/-- Canonical bounded complex-linear conormal trace with exact nu^-1/2 order. -/
def annularFluxTrace (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (endpoint : Fin 2) :
    annularFluxWeakGraph lower positive →L[ℂ] AnnularBoundary :=
  (annularFluxTraceLinear lower positive bounded endpoint).mkContinuous (2 * annularFluxTraceConstant lower)
    (annularFluxTraceLinear_bound lower positive bounded endpoint)

theorem annularFluxTrace_bound (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (endpoint : Fin 2) (data : annularFluxWeakGraph lower positive) :
    ‖annularFluxTrace lower positive bounded endpoint data‖ ≤
      annularFluxTraceConstant lower * (‖data.val.1‖ + ‖data.val.2‖) :=
  annularFluxTraceFamily_bound lower positive bounded endpoint data

theorem annularFluxTrace_apply (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (endpoint : Fin 2) (data : annularFluxWeakGraph lower positive) (mode : HighAnnularMode) :
    annularFluxTrace lower positive bounded endpoint data mode =
      (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2))⁻¹ •
        annularFluxSection lower positive bounded data mode
          ⟨radialEndpointRadius lower endpoint, radialEndpointRadius_mem lower bounded.le endpoint⟩ :=
  annularFluxTraceCoefficient_section lower positive bounded endpoint data mode

/-- The boundary norm is the literal negative half-order square sum. -/
theorem annularFluxTrace_norm_sq (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (endpoint : Fin 2) (data : annularFluxWeakGraph lower positive) :
    ‖annularFluxTrace lower positive bounded endpoint data‖ ^ 2 =
      ∑' mode : HighAnnularMode, (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)⁻¹ *
        ‖weightedRadialTrace 1 lower positive bounded endpoint
          (annularFluxRadialGraph lower positive bounded data mode)‖ ^ 2 := by
  have formula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (annularFluxTrace lower positive bounded endpoint data)
  norm_num at formula
  refine formula.trans (tsum_congr (fun mode => ?_))
  exact annularFluxTraceCoefficient_norm_sq lower positive bounded endpoint data mode

end Grad.AnnularFluxTrace
