import AEE11LiteralSmoothModeSquares

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators ENNReal
namespace Grad.AnnularLowCompletion
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowVolterra
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- AEC coercivity applied to each actual smooth pair with its own actual
reference residual. No source equation or trace is assumed. -/
theorem lowCorePair_coercivity (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower ≤ 1)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (mode : LowAnnularMode) :
    lowCoreGraphSquare length lower core (0, mode) + lowCoreGraphSquare length lower core (1, mode) ≤
      lowReferenceGraphConstant parameters length *
        (lowCoreDataSquare parameters length lower positive core (0, mode) +
          lowCoreDataSquare parameters length lower positive core (1, mode)) := by
  have estimate := lowReferenceGraph_integrated_bound parameters length lower lengthPositive mode positive bounded
    (core (0, mode)).val.val.1 (core (1, mode)).val.val.1
    (lowCoreResidualCurve parameters length lower positive core (0, mode))
    (lowCoreResidualCurve parameters length lower positive core (1, mode))
    (fun _ _ => (lowCoreResidualCurve parameters length lower positive core (0, mode)).continuous.continuousAt)
    (fun _ _ => (lowCoreResidualCurve parameters length lower positive core (1, mode)).continuous.continuousAt)
    (fun radius member => lowCore_reference_first parameters length lower positive core mode radius member.1)
    (fun radius member => lowCore_reference_second parameters length lower positive core mode radius member.1)
  have graphEquality : (∫ radius in lower..1, radius ^ (-(7 / 2 : ℝ)) *
      (‖(core (0, mode)).val.val.1 radius‖ ^ 2 + ‖(core (1, mode)).val.val.1 radius‖ ^ 2 +
        ‖(lowMu length radius mode.val.2)⁻¹ • deriv (core (0, mode)).val.val.1 radius‖ ^ 2 +
        ‖(lowMu length radius mode.val.2)⁻¹ • deriv (core (1, mode)).val.val.1 radius‖ ^ 2)) =
      lowCoreGraphSquare length lower core (0, mode) + lowCoreGraphSquare length lower core (1, mode) := by
    unfold lowCoreGraphSquare
    rw [← intervalIntegral.integral_add
      (lowCoreGraphDensity_integrable length lower positive bounded core (0, mode))
      (lowCoreGraphDensity_integrable length lower positive bounded core (1, mode))]
    apply intervalIntegral.integral_congr
    intro radius _
    dsimp only [lowCoreGraphDensity]
    rw [((core (0, mode)).val.property radius).deriv, ((core (1, mode)).val.property radius).deriv]
    ring
  have dataEquality : lowPairEnergy length lower mode ((core (0, mode)).val.val.1 lower) ((core (1, mode)).val.val.1 lower) +
      (∫ radius in lower..1, radius ^ (-(7 / 2 : ℝ)) *
        (‖lowCoreResidualCurve parameters length lower positive core (0, mode) radius‖ ^ 2 +
          ‖lowCoreResidualCurve parameters length lower positive core (1, mode) radius‖ ^ 2)) =
      lowCoreDataSquare parameters length lower positive core (0, mode) +
        lowCoreDataSquare parameters length lower positive core (1, mode) := by
    have forceEquality : (∫ radius in lower..1, radius ^ (-(7 / 2 : ℝ)) *
        (‖lowCoreResidualCurve parameters length lower positive core (0, mode) radius‖ ^ 2 +
          ‖lowCoreResidualCurve parameters length lower positive core (1, mode) radius‖ ^ 2)) =
        (∫ radius in lower..1, lowCoreForceDensity parameters length lower positive core (0, mode) radius) +
          ∫ radius in lower..1, lowCoreForceDensity parameters length lower positive core (1, mode) radius := by
      rw [← intervalIntegral.integral_add
        (lowCoreForceDensity_integrable parameters length lower positive bounded core (0, mode))
        (lowCoreForceDensity_integrable parameters length lower positive bounded core (1, mode))]
      apply intervalIntegral.integral_congr
      intro radius _
      dsimp only [lowCoreForceDensity]
      ring
    rw [forceEquality]
    unfold lowCoreDataSquare lowCoreIncomingSquare lowPairEnergy
    ring
  rw [graphEquality, dataEquality] at estimate
  exact estimate

end Grad.AnnularLowCompletion
