import AKS8HomogeneousGraphLocality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology
namespace Grad.AnnularWeightedUniqueness
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularReconstruction
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularForwardDatum Grad.AnnularForwardTraces Grad.AnnularStrongOrbit
open Grad.AnnularCoupledInverse Grad.AnnularRestriction Grad.AnnularExhaustionEstimate
open Grad.AnnularIncomingIntegrability Grad.SourceCollarDivision Grad.AnnularSourceGraph
open Grad.AnnularCurrentSource Grad.AnnularVariational Grad.AnnularLowEnergy Grad.AnnularTiltedReference
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule
  Grad.AnnularStrongOrbit.knownAmbientNormed Grad.AnnularStrongOrbit.knownAmbientSeminormed
  Grad.AnnularStrongOrbit.knownAmbientRealNormed Grad.AnnularStrongOrbit.knownAmbientRealModule
  Grad.AnnularStrongOrbit.strongCarrierNormed Grad.AnnularStrongOrbit.strongCarrierSeminormed
  Grad.AnnularStrongOrbit.strongCarrierRealNormed Grad.AnnularStrongOrbit.strongCarrierRealModule

open Grad.AnnularFullGraph Grad.AnnularWeakExhaustion

open Grad.ActualAnnularExhaustion

theorem originalWeightedRetainedObservation_restrict (parameters : PhaseParameters) (lower upper length : ℝ)
    (positiveLower : 0 < lower) (positiveUpper : 0 < upper) (boundedUpper : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (point : OriginalFiveBlockAmbient parameters lower length positiveLower) :
    originalWeightedRetainedObservation parameters upper length positiveUpper boundedUpper.le lengthPositive
      (originalFiveBlockRestriction parameters lower upper length positiveLower positiveUpper boundedUpper lengthPositive included point) =
    coupledEndpointRestriction lower upper length positiveLower positiveUpper boundedUpper lengthPositive included
      (originalWeightedRetainedObservation parameters lower length positiveLower (included.trans boundedUpper.le) lengthPositive point) :=
  originalRetainedRestriction_weighted parameters lower upper length positiveLower positiveUpper boundedUpper lengthPositive included point.ofLp.1

/-- Local homogeneous uniqueness estimate using the solution's own incoming
trace at the intermediate context radius. All middle retained norms stay in
the SAME context-indexed carrier, and restriction to the outer collar is native. -/
theorem homogeneousRestriction_bound (parameters : PhaseParameters) (length compact lower upper : ℝ)
    (context : Grad.AnnularCrossOrbit.CoupledCoordinateContext parameters length compact)
    (positiveLower : 0 < lower) (positiveUpper : 0 < upper) (upperHalf : upper ≤ 1 / 2)
    (first : lower ≤ context.lower) (second : context.lower ≤ upper)
    (point : OriginalFiveBlockAmbient parameters lower length positiveLower)
    (equation : point ∈ OriginalObservedEquationGraph parameters length compact lower positiveLower
      (first.trans context.lowerHalf) context.lengthPositive context.widthHalf context.widthLength context.state)
    (sources : point.ofLp.2 = 0)
    (outer : originalOuterBoundaryTrace parameters length compact lower positiveLower (first.trans context.lowerHalf)
      context.lengthPositive context.state (point.ofLp.1,point.ofLp.2.ofLp.1) = 0) :
    originalWeightedRetainedNorm parameters upper length positiveUpper (upperHalf.trans (by norm_num)) context.lengthPositive
      (originalFiveBlockRestriction parameters lower upper length positiveLower positiveUpper (upperHalf.trans_lt (by norm_num))
        context.lengthPositive (first.trans second) point).ofLp.1 ≤
      2 * Grad.AnnularFullSource.independentCoupledDataConstant parameters length compact *
      ‖coupledIncomingTrace context.lower length context.positive (context.lowerHalf.trans_lt (by norm_num)) context.lengthPositive
        (coupledEndpointRestriction lower context.lower length positiveLower context.positive (context.lowerHalf.trans_lt (by norm_num))
          context.lengthPositive first
          (originalWeightedRetainedObservation parameters lower length positiveLower ((first.trans context.lowerHalf).trans (by norm_num))
            context.lengthPositive point))‖ := by
  let middleBounded : context.lower < 1 := context.lowerHalf.trans_lt (by norm_num)
  let upperBounded : upper < 1 := upperHalf.trans_lt (by norm_num)
  let next := originalFiveBlockRestriction parameters lower context.lower length positiveLower context.positive middleBounded context.lengthPositive first point
  have conditions := originalHomogeneousGraph_restrict parameters length compact lower context.lower positiveLower context.positive context.lowerHalf
    first context.lengthPositive context.widthHalf context.widthLength context.state context.small point equation sources outer
  have estimate := originalHomogeneousGraph_bound parameters length compact context next conditions.1 conditions.2.1 conditions.2.2
  have contraction := originalWeightedRetained_restriction_bound parameters context.lower upper length context.positive positiveUpper upperBounded context.lengthPositive second next
  dsimp only [next] at estimate contraction
  have composed := originalFiveBlockRestriction_comp parameters lower context.lower upper length positiveLower context.positive positiveUpper
    upperBounded context.lengthPositive first second point
  have normSame := congrArg (fun item : OriginalFiveBlockAmbient parameters upper length positiveUpper =>
    originalWeightedRetainedNorm parameters upper length positiveUpper upperBounded.le context.lengthPositive item.ofLp.1) composed
  have sameIncoming := congrArg (fun item : CoupledSpace context.lower length context.positive context.lengthPositive =>
      ‖coupledIncomingTrace context.lower length context.positive middleBounded context.lengthPositive item‖)
    (originalWeightedRetainedObservation_restrict parameters lower context.lower length positiveLower context.positive middleBounded context.lengthPositive first point)
  have weightedIncoming := congrArg
    (fun value : ℝ => 2 * Grad.AnnularFullSource.independentCoupledDataConstant parameters length compact * value) sameIncoming
  linarith only [normSame, contraction, estimate, weightedIncoming]

end Grad.AnnularWeightedUniqueness
