import AAQ6LiteralFluxWeakGraph

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

def annularFluxTraceConstant (lower : ℝ) : ℝ := Real.sqrt (collarTraceConstant lower / lower)

theorem annularFluxTraceConstant_nonnegative (lower : ℝ) : 0 ≤ annularFluxTraceConstant lower := Real.sqrt_nonneg _

def annularFluxTraceCoefficient (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (endpoint : Fin 2) (data : annularFluxWeakGraph lower positive) (mode : HighAnnularMode) : ComplexEuclidean 1 :=
  (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2))⁻¹ •
    weightedRadialTrace 1 lower positive bounded endpoint (annularFluxRadialGraph lower positive bounded data mode)

theorem annularFluxTraceCoefficient_norm_sq (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (endpoint : Fin 2) (data : annularFluxWeakGraph lower positive) (mode : HighAnnularMode) :
    ‖annularFluxTraceCoefficient lower positive bounded endpoint data mode‖ ^ 2 =
      (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)⁻¹ *
        ‖weightedRadialTrace 1 lower positive bounded endpoint
          (annularFluxRadialGraph lower positive bounded data mode)‖ ^ 2 := by
  unfold annularFluxTraceCoefficient
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), mul_pow, inv_pow,
    Real.sq_sqrt (annularFrequency_pos mode).le]

theorem annularFluxTraceCoefficient_bound_sq (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (endpoint : Fin 2) (data : annularFluxWeakGraph lower positive) (mode : HighAnnularMode) :
    ‖annularFluxTraceCoefficient lower positive bounded endpoint data mode‖ ^ 2 ≤
      (collarTraceConstant lower / lower) * (‖data.val.1 mode‖ ^ 2 + ‖data.val.2 mode‖ ^ 2) := by
  rw [annularFluxTraceCoefficient_norm_sq]
  have estimate := weightedRadialTrace_frequency_bound_sq 1 lower
    (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) positive bounded
    (annularFrequency_one_le _ _) endpoint (annularFluxRadialGraph lower positive bounded data mode)
  rw [annularFluxRadialGraph_value, annularFluxRadialGraph_slope, norm_smul,
    Real.norm_of_nonneg (annularFrequency_pos mode).le, mul_pow] at estimate
  have cancellation : (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)⁻¹ ^ 2 *
      ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ 2 * ‖data.val.2 mode‖ ^ 2) =
      ‖data.val.2 mode‖ ^ 2 := by
    have nonzero := (annularFrequency_pos mode).ne'
    field_simp
  rwa [cancellation] at estimate

theorem annularFluxTraceCoefficient_bound (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (endpoint : Fin 2) (data : annularFluxWeakGraph lower positive) (mode : HighAnnularMode) :
    ‖annularFluxTraceCoefficient lower positive bounded endpoint data mode‖ ≤
      annularFluxTraceConstant lower * (‖data.val.1 mode‖ + ‖data.val.2 mode‖) := by
  have constantNonnegative : 0 ≤ collarTraceConstant lower / lower :=
    div_nonneg (zero_le_one.trans (collarTraceConstant_one_le bounded)) positive.le
  have square := Real.sq_sqrt constantNonnegative
  have estimate := annularFluxTraceCoefficient_bound_sq lower positive bounded endpoint data mode
  have nonnegative := Real.sqrt_nonneg (collarTraceConstant lower / lower)
  unfold annularFluxTraceConstant
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg nonnegative (add_nonneg (norm_nonneg _) (norm_nonneg _)))).mp
  rw [mul_pow, square]
  exact estimate.trans (mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg (data.val.1 mode), norm_nonneg (data.val.2 mode)]) constantNonnegative)

section NormFamily
variable {Index E : Type*} [NormedAddCommGroup E]

def lpNormFamily (field : lp (fun _ : Index => E) 2) : lp (fun _ : Index => ℝ) 2 :=
  ⟨fun index => ‖field index‖, (lp.memℓp field).mono' (fun index => by simp only [Real.norm_eq_abs, abs_norm]; exact le_rfl)⟩

theorem lpNormFamily_norm (field : lp (fun _ : Index => E) 2) : ‖lpNormFamily field‖ = ‖field‖ := by
  apply le_antisymm
  · apply lp.norm_mono (by norm_num)
    intro index
    change ‖‖field index‖‖ ≤ ‖field index‖
    rw [norm_norm]
  · apply lp.norm_mono (by norm_num)
    intro index
    change ‖field index‖ ≤ ‖‖field index‖‖
    rw [norm_norm]
end NormFamily

def annularFluxTraceFamily (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (endpoint : Fin 2) (data : annularFluxWeakGraph lower positive) : AnnularBoundary :=
  ⟨annularFluxTraceCoefficient lower positive bounded endpoint data,
    (lp.memℓp ((annularFluxTraceConstant lower) • (lpNormFamily data.val.1 + lpNormFamily data.val.2))).mono'
      (fun mode => by
        change ‖annularFluxTraceCoefficient lower positive bounded endpoint data mode‖ ≤
          ‖annularFluxTraceConstant lower • (‖data.val.1 mode‖ + ‖data.val.2 mode‖)‖
        rw [norm_smul, Real.norm_of_nonneg (annularFluxTraceConstant_nonnegative lower),
          Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
        exact annularFluxTraceCoefficient_bound lower positive bounded endpoint data mode)⟩

theorem annularFluxTraceFamily_bound (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (endpoint : Fin 2) (data : annularFluxWeakGraph lower positive) :
    ‖annularFluxTraceFamily lower positive bounded endpoint data‖ ≤
      annularFluxTraceConstant lower * (‖data.val.1‖ + ‖data.val.2‖) := by
  calc
    _ ≤ ‖annularFluxTraceConstant lower • (lpNormFamily data.val.1 + lpNormFamily data.val.2)‖ := by
      apply lp.norm_mono (by norm_num)
      intro mode
      change ‖annularFluxTraceCoefficient lower positive bounded endpoint data mode‖ ≤
        ‖annularFluxTraceConstant lower • (‖data.val.1 mode‖ + ‖data.val.2 mode‖)‖
      rw [norm_smul, Real.norm_of_nonneg (annularFluxTraceConstant_nonnegative lower),
        Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact annularFluxTraceCoefficient_bound lower positive bounded endpoint data mode
    _ = annularFluxTraceConstant lower * ‖lpNormFamily data.val.1 + lpNormFamily data.val.2‖ := by
      rw [norm_smul, Real.norm_of_nonneg (annularFluxTraceConstant_nonnegative lower)]
    _ ≤ annularFluxTraceConstant lower * (‖lpNormFamily data.val.1‖ + ‖lpNormFamily data.val.2‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.sqrt_nonneg _)
    _ = _ := by rw [lpNormFamily_norm, lpNormFamily_norm]

end Grad.AnnularFluxTrace
