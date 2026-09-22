import AEM1ExactLowHalfCollarEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCrossMaps
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.AnnularSourceGraph Grad.AnnularFluxTrace Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

def lowCanonicalEndpointLinear (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (endpoint : Fin 2) (index : LowAnnularIndex) :
    lowEnergyGraph lower length positive →ₗ[ℂ] ComplexEuclidean 1 where
  toFun field := lowEnergyEndpoint lower length positive bounded endpoint field index
  map_add' first second := by
    unfold lowEnergyEndpoint
    rw [lowEnergySection_add]
    rfl
  map_smul' scalar field := by
    unfold lowEnergyEndpoint
    rw [lowEnergySection_smul]
    rfl

theorem lowCanonicalEndpoint_fixed_bound (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (endpoint : Fin 2) (index : LowAnnularIndex) (field : lowEnergyGraph lower length positive) :
    ‖lowEnergyEndpoint lower length positive bounded endpoint field index‖ ≤
      Real.sqrt (lowMu length lower index.2.val.2 * (collarTraceConstant lower / lower)) * ‖field‖ := by
  have muPositive := lowMu_pos length lower index.2.val.2 positive
  have traceNonnegative : 0 ≤ collarTraceConstant lower / lower :=
    div_nonneg (zero_le_one.trans (collarTraceConstant_one_le bounded)) positive.le
  have actual := mul_le_mul_of_nonneg_left (lowEndpoint_mu_bound_sq lower length positive bounded endpoint field index) muPositive.le
  rw [← mul_assoc, mul_inv_cancel₀ muPositive.ne', one_mul] at actual
  have first := lp.norm_apply_le_norm (p := 2) (by norm_num) (field.val 0) index
  have second := lp.norm_apply_le_norm (p := 2) (by norm_num) (field.val 1) index
  have firstSq := pow_le_pow_left₀ (norm_nonneg _) first 2
  have secondSq := pow_le_pow_left₀ (norm_nonneg _) second 2
  have graph := lowEnergyGraph_norm_sq lower length positive field
  have squares : ‖field.val 0 index‖ ^ 2 + ‖field.val 1 index‖ ^ 2 ≤ ‖field‖ ^ 2 := by linarith
  have bound := actual.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left squares traceNonnegative) muPositive.le)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg field))).mp
  rw [mul_pow, Real.sq_sqrt (mul_nonneg muPositive.le traceNonnegative)]
  simpa only [mul_assoc] using bound

/-- Continuity of the SAME canonical endpoint, for fixed ell only. This
is used to pass the independent uniform outer estimate through ADY density. -/
def lowCanonicalEndpoint (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (endpoint : Fin 2) (index : LowAnnularIndex) :
    lowEnergyGraph lower length positive →L[ℂ] ComplexEuclidean 1 :=
  (lowCanonicalEndpointLinear lower length positive bounded endpoint index).mkContinuous
    (Real.sqrt (lowMu length lower index.2.val.2 * (collarTraceConstant lower / lower)))
    (lowCanonicalEndpoint_fixed_bound lower length positive bounded endpoint index)

def lowModalStoredCoordinate (lower length : ℝ) (positive : 0 < lower) (row : Fin 2) (index : LowAnnularIndex) :
    lowEnergyGraph lower length positive →L[ℂ] CollarL2 (ComplexEuclidean 1) lower :=
  (lp.evalCLM ℂ (fun _ : LowAnnularIndex => CollarL2 (ComplexEuclidean 1) lower) 2 index).comp
    (lowStoredCoordinate lower length positive row)

end Grad.AnnularCrossMaps
