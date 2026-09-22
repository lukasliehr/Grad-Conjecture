import AEI29OriginalPhysicalCurrentInverseConsumer

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

/-- Exact restriction of the original rho-weighted smooth low energy to
the fixed terminal half collar. No derivative weight is replaced. -/
theorem lowCoreGraphSquare_half_le (lower length : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (index : LowAnnularIndex) :
    lowCoreGraphSquare length (1 / 2) core index ≤ lowCoreGraphSquare length lower core index := by
  apply intervalIntegral.integral_mono_interval lowerHalf (by norm_num) le_rfl
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius inside
    exact mul_nonneg (Real.rpow_pos_of_pos (positive.trans inside.1) _).le
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  · exact lowCoreGraphDensity_integrable length lower positive (lowerHalf.trans (by norm_num)) core index

theorem lowSmoothGraph_outer_half_bound_sq (lower length : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (index : LowAnnularIndex) :
    (lowMu length (1 / 2) index.2.val.2)⁻¹ *
      ‖lowEnergyEndpoint lower length positive (lowerHalf.trans_lt (by norm_num)) 1
        (lowSmoothGraph lower length positive (lowerHalf.trans_lt (by norm_num)) core) index‖ ^ 2 ≤
    (collarTraceConstant (1 / 2) / (1 / 2)) *
      (‖(lowSmoothGraph lower length positive (lowerHalf.trans_lt (by norm_num)) core).val 0 index‖ ^ 2 +
       ‖(lowSmoothGraph lower length positive (lowerHalf.trans_lt (by norm_num)) core).val 1 index‖ ^ 2) := by
  have bound := lowEndpoint_mu_bound_sq (1 / 2) length (by norm_num) (by norm_num) 1
    (lowSmoothGraph (1 / 2) length (by norm_num) (by norm_num) core) index
  have same : lowEnergyEndpoint (1 / 2) length (by norm_num) (by norm_num) 1
      (lowSmoothGraph (1 / 2) length (by norm_num) (by norm_num) core) index =
    lowEnergyEndpoint lower length positive (lowerHalf.trans_lt (by norm_num)) 1
      (lowSmoothGraph lower length positive (lowerHalf.trans_lt (by norm_num)) core) index := by
    unfold lowEnergyEndpoint
    rw [lowSmoothGraph_section, lowSmoothGraph_section]
    rfl
  rw [same, ← lowCoreGraphSquare_stored] at bound
  rw [← lowCoreGraphSquare_stored]
  exact bound.trans (mul_le_mul_of_nonneg_left (lowCoreGraphSquare_half_le lower length positive lowerHalf core index)
    (div_nonneg (zero_le_one.trans (collarTraceConstant_one_le (by norm_num : (1 / 2 : ℝ) < 1))) (by norm_num)))

end Grad.AnnularCrossMaps
