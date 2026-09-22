import AKS2ActualHomogeneousSolutionBound

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

/-- The homogeneous estimate applies directly to the actual full observed
equation graph, with all copied source blocks zero and the full outer row zero. -/
theorem originalHomogeneousGraph_bound (parameters : PhaseParameters) (length compact : ℝ)
    (context : Grad.AnnularCrossOrbit.CoupledCoordinateContext parameters length compact)
    (point : OriginalFiveBlockAmbient parameters context.lower length context.positive)
    (equation : point ∈ OriginalObservedEquationGraph parameters length compact context.lower context.positive context.lowerHalf
      context.lengthPositive context.widthHalf context.widthLength context.state)
    (sources : point.ofLp.2 = 0)
    (outer : originalOuterBoundaryTrace parameters length compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.state (point.ofLp.1,point.ofLp.2.ofLp.1) = 0) :
    originalWeightedRetainedNorm parameters context.lower length context.positive
      (context.lowerHalf.trans (by norm_num)) context.lengthPositive point.ofLp.1 ≤
      2 * Grad.AnnularFullSource.independentCoupledDataConstant parameters length compact *
      ‖coupledIncomingTrace context.lower length context.positive (context.lowerHalf.trans_lt (by norm_num)) context.lengthPositive
        (originalWeightedRetainedObservation parameters context.lower length context.positive
          (context.lowerHalf.trans (by norm_num)) context.lengthPositive point)‖ := by
  obtain ⟨pair,actual,rfl⟩ := equation
  have boundary := originalBoundaryTrace_of_equation parameters length compact context.lower context.positive context.lowerHalf
    context.lengthPositive context.state context.widthHalf context.widthLength context.small pair.1 pair.2 actual
  have outerData : pair.1.val.ofLp.2.ofLp.1 = 0 :=
    (congrArg (fun item : OriginalBoundaryCoordinates parameters => item.ofLp.1) boundary).symm.trans outer
  exact originalHomogeneousSolution_bound parameters length compact context pair.1 pair.2 actual sources outerData

/-- Restriction is a contraction in the native weighted retained norm. The
endpoint-dependent original coordinate equivalence supplies only the identity. -/
theorem originalWeightedRetained_restriction_bound (parameters : PhaseParameters) (lower upper length : ℝ)
    (positiveLower : 0 < lower) (positiveUpper : 0 < upper) (boundedUpper : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (point : OriginalFiveBlockAmbient parameters lower length positiveLower) :
    originalWeightedRetainedNorm parameters upper length positiveUpper boundedUpper.le lengthPositive
      (originalFiveBlockRestriction parameters lower upper length positiveLower positiveUpper boundedUpper lengthPositive included point).ofLp.1 ≤
    originalWeightedRetainedNorm parameters lower length positiveLower (included.trans boundedUpper.le) lengthPositive point.ofLp.1 := by
  have coordinate := (originalFiveBlockRestriction_coordinates parameters lower upper length positiveLower positiveUpper
    boundedUpper lengthPositive included point).1
  have coordinateNorm := congrArg (originalWeightedRetainedNorm parameters upper length positiveUpper boundedUpper.le lengthPositive) coordinate
  have same := congrArg (fun field : CoupledSpace upper length positiveUpper lengthPositive => ‖field‖)
    (originalRetainedRestriction_weighted parameters lower upper length positiveLower positiveUpper boundedUpper lengthPositive included point.ofLp.1)
  have native := same.trans_le (coupledEndpointRestriction_bound lower upper length positiveLower positiveUpper boundedUpper lengthPositive included _)
  exact coordinateNorm.trans_le native

end Grad.AnnularWeightedUniqueness
