import AEM2ActualCanonicalEndpointContinuity

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

/-- BE20's decisive modal estimate on arbitrary elements of the independent
low graph. The bound is fixed at[1/2,1], while the endpoint is the original one. -/
theorem lowCanonicalOuter_half_bound_sq (lower length : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    (lowMu length (1 / 2) index.2.val.2)⁻¹ *
      ‖lowEnergyEndpoint lower length positive (lowerHalf.trans_lt (by norm_num)) 1 field index‖ ^ 2 ≤
    (collarTraceConstant (1 / 2) / (1 / 2)) *
      (‖field.val 0 index‖ ^ 2 + ‖field.val 1 index‖ ^ 2) := by
  change (lowMu length (1 / 2) index.2.val.2)⁻¹ *
      ‖lowCanonicalEndpoint lower length positive (lowerHalf.trans_lt (by norm_num)) 1 index field‖ ^ 2 ≤
    (collarTraceConstant (1 / 2) / (1 / 2)) *
      (‖lowModalStoredCoordinate lower length positive 0 index field‖ ^ 2 +
       ‖lowModalStoredCoordinate lower length positive 1 index field‖ ^ 2)
  apply isClosed_property (lowSmoothGraph_denseRange lower length positive (lowerHalf.trans_lt (by norm_num)))
    (isClosed_le
      (continuous_const.mul ((lowCanonicalEndpoint lower length positive (lowerHalf.trans_lt (by norm_num)) 1 index).continuous.norm.pow 2))
      (continuous_const.mul (((lowModalStoredCoordinate lower length positive 0 index).continuous.norm.pow 2).add
        ((lowModalStoredCoordinate lower length positive 1 index).continuous.norm.pow 2)))) _ field
  intro core
  exact lowSmoothGraph_outer_half_bound_sq lower length positive lowerHalf core index

def lowOuterHalfConstant : ℝ := Real.sqrt (collarTraceConstant (1 / 2) / (1 / 2))

theorem lowOuterHalfConstant_nonnegative : 0 ≤ lowOuterHalfConstant := Real.sqrt_nonneg _

def lowOuterHalfCoefficient (lower length : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) : ComplexEuclidean 1 :=
  (Real.sqrt (lowMu length (1 / 2) index.2.val.2))⁻¹ •
    lowEnergyEndpoint lower length positive (lowerHalf.trans_lt (by norm_num)) 1 field index

theorem lowOuterHalfCoefficient_bound (lower length : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    ‖lowOuterHalfCoefficient lower length positive lowerHalf field index‖ ≤
      lowOuterHalfConstant * (‖field.val 0 index‖ + ‖field.val 1 index‖) := by
  have squared := lowCanonicalOuter_half_bound_sq lower length positive lowerHalf field index
  have nonnegative : 0 ≤ collarTraceConstant (1 / 2) / (1 / 2) :=
    div_nonneg (zero_le_one.trans (collarTraceConstant_one_le (by norm_num : (1 / 2 : ℝ) < 1))) (by norm_num)
  have scalarNorm : ‖lowOuterHalfCoefficient lower length positive lowerHalf field index‖ ^ 2 =
      (lowMu length (1 / 2) index.2.val.2)⁻¹ *
        ‖lowEnergyEndpoint lower length positive (lowerHalf.trans_lt (by norm_num)) 1 field index‖ ^ 2 := by
    rw [lowOuterHalfCoefficient, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), mul_pow,
      inv_pow, Real.sq_sqrt (lowMu_nonneg _ _ _)]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg lowOuterHalfConstant_nonnegative (add_nonneg (norm_nonneg _) (norm_nonneg _)))).mp
  rw [mul_pow, lowOuterHalfConstant, Real.sq_sqrt nonnegative, scalarNorm]
  exact squared.trans (mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg (field.val 0 index), norm_nonneg (field.val 1 index)]) nonnegative)

end Grad.AnnularCrossMaps
