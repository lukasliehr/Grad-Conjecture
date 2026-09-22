import AEE12ActualSmoothPairCoercivity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators ENNReal
namespace Grad.AnnularLowCompletion
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowVolterra
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem lowIntegral_congr_ae (lower : ℝ) (bounded : lower ≤ 1) (first second : ℝ → ℝ)
    (same : first =ᵐ[volume.restrict (Icc lower 1)] second) :
    (∫ radius in lower..1, first radius) = ∫ radius in lower..1, second radius := by
  rw [intervalIntegral.integral_of_le bounded, intervalIntegral.integral_of_le bounded,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  exact MeasureTheory.integral_congr_ae same

theorem lowSmooth_storedValue_norm_sq (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (index : LowAnnularIndex) :
    ‖(lowSmoothGraph lower length positive bounded core).val 0 index‖ ^ 2 =
      ∫ radius in lower..1, radius ^ (-(7 / 2 : ℝ)) * ‖(core index).val.val.1 radius‖ ^ 2 := by
  rw [lowWeighted_norm_sq lower positive bounded.le]
  apply lowIntegral_congr_ae lower bounded.le
  filter_upwards [lowSmoothGraph_value_ae lower length positive bounded core index] with radius same
  change radius ^ (-(7 / 2 : ℝ)) * ‖lowEnergyValue lower positive index
    (lowSmoothGraph lower length positive bounded core).val radius‖ ^ 2 = _
  rw [same]

theorem lowSmooth_storedSlope_norm_sq (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (index : LowAnnularIndex) :
    ‖(lowSmoothGraph lower length positive bounded core).val 1 index‖ ^ 2 =
      ∫ radius in lower..1, radius ^ (-(7 / 2 : ℝ)) *
        ‖(lowMu length radius index.2.val.2)⁻¹ • (core index).val.val.2 radius‖ ^ 2 := by
  rw [lowWeighted_norm_sq lower positive bounded.le,
    ← lowEnergy_normalized_derivative lower length positive (lowSmoothGraph lower length positive bounded core).val index]
  apply lowIntegral_congr_ae lower bounded.le
  filter_upwards [lowSmoothGraph_normalizedDerivative_ae lower length positive bounded core index] with radius same
  rw [same]

theorem lowCoreGraphSquare_stored (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (index : LowAnnularIndex) :
    lowCoreGraphSquare length lower core index =
      ‖(lowSmoothGraph lower length positive bounded core).val 0 index‖ ^ 2 +
        ‖(lowSmoothGraph lower length positive bounded core).val 1 index‖ ^ 2 := by
  rw [lowSmooth_storedValue_norm_sq, lowSmooth_storedSlope_norm_sq]
  have valueIntegrable : IntervalIntegrable (fun radius => radius ^ (-(7 / 2 : ℝ)) *
      ‖(core index).val.val.1 radius‖ ^ 2) volume lower 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le bounded.le]
    intro radius member
    exact ((Real.hasDerivAt_rpow_const (x := radius) (p := -(7 / 2 : ℝ))
      (Or.inl (positive.trans_le member.1).ne')).continuousAt.mul
      ((core index).val.val.1.continuous.continuousAt.norm.pow 2)).continuousWithinAt
  have slopeIntegrable : IntervalIntegrable (fun radius => radius ^ (-(7 / 2 : ℝ)) *
      ‖(lowMu length radius index.2.val.2)⁻¹ • (core index).val.val.2 radius‖ ^ 2) volume lower 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le bounded.le]
    intro radius member
    have normalized := (lowMuInverse_hasDerivAt length radius index.2.val.2 (positive.trans_le member.1)).continuousAt.smul
      (core index).val.val.2.continuous.continuousAt
    exact ((Real.hasDerivAt_rpow_const (x := radius) (p := -(7 / 2 : ℝ))
      (Or.inl (positive.trans_le member.1).ne')).continuousAt.mul (normalized.norm.pow 2)).continuousWithinAt
  rw [← intervalIntegral.integral_add valueIntegrable slopeIntegrable]
  apply intervalIntegral.integral_congr
  intro radius _
  dsimp only [lowCoreGraphSquare, lowCoreGraphDensity]
  ring

theorem lowCoreDataSquare_stored (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (index : LowAnnularIndex) :
    lowCoreDataSquare parameters length lower positive core index =
      ‖(lowReferenceDataOperator parameters length lower lengthPositive positive bounded
        (lowSmoothGraph lower length positive bounded core)).ofLp.1 index‖ ^ 2 +
      ‖(lowReferenceDataOperator parameters length lower lengthPositive positive bounded
        (lowSmoothGraph lower length positive bounded core)).ofLp.2 index‖ ^ 2 := by
  have residualNorm : ‖(lowReferenceDataOperator parameters length lower lengthPositive positive bounded
      (lowSmoothGraph lower length positive bounded core)).ofLp.1 index‖ ^ 2 =
      ∫ radius in lower..1, lowCoreForceDensity parameters length lower positive core index radius := by
    rw [lowWeighted_norm_sq lower positive bounded.le]
    apply lowIntegral_congr_ae lower bounded.le
    filter_upwards [lowSmoothGraph_dataResidual_ae parameters length lower lengthPositive positive bounded core index] with radius same
    change radius ^ (-(7 / 2 : ℝ)) * ‖lowDataResidual lower positive
      (lowReferenceDataOperator parameters length lower lengthPositive positive bounded
        (lowSmoothGraph lower length positive bounded core)) index radius‖ ^ 2 = _
    rw [same]
    rfl
  have incomingNorm := lowIncomingCoefficient_norm_sq lower length positive bounded
    (lowSmoothGraph lower length positive bounded core) index
  change ‖(lowReferenceDataOperator parameters length lower lengthPositive positive bounded
      (lowSmoothGraph lower length positive bounded core)).ofLp.2 index‖ ^ 2 =
      lowEnergyDensity length lower index.2.val.2 *
        ‖lowEnergyEndpoint lower length positive bounded 0 (lowSmoothGraph lower length positive bounded core) index‖ ^ 2 at incomingNorm
  unfold lowEnergyEndpoint at incomingNorm
  rw [lowSmoothGraph_section] at incomingNorm
  rw [residualNorm, incomingNorm]
  unfold lowCoreDataSquare lowCoreIncomingSquare
  exact add_comm _ _

end Grad.AnnularLowCompletion
