import AKS1ExactHomogeneousIncomingNorm

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

/-- Exact original homogeneous solution estimate. The boundary values are
its own traces, recovered from the full actual coupled equation. -/
theorem originalHomogeneousSolution_bound (parameters : PhaseParameters) (length compact : ℝ)
    (context : Grad.AnnularCrossOrbit.CoupledCoordinateContext parameters length compact)
    (data : OriginalStrongCarrier parameters context.lower 0 0)
    (candidate : OriginalCoupledSpace context.lower length context.positive)
    (equation : OriginalStrongCoupledEquation parameters length compact context.lower context.positive context.lowerHalf
      context.lengthPositive context.widthHalf context.widthLength context.state data candidate)
    (sources : data.val.ofLp.1 = 0) (outer : data.val.ofLp.2.ofLp.1 = 0) :
    originalWeightedRetainedNorm parameters context.lower length context.positive
      (context.lowerHalf.trans (by norm_num)) context.lengthPositive candidate ≤
      2 * Grad.AnnularFullSource.independentCoupledDataConstant parameters length compact *
      ‖coupledIncomingTrace context.lower length context.positive (context.lowerHalf.trans_lt (by norm_num)) context.lengthPositive
        (originalWeightedRetained parameters context.lower length context.positive
          (context.lowerHalf.trans (by norm_num)) context.lengthPositive candidate)‖ := by
  have same := originalSharedResponse_unique parameters length compact context.lower context.positive context.lowerHalf
    context.lengthPositive context.widthHalf context.widthLength context.state context.small data candidate equation
  have estimate := originalSharedResponse_uniform_base parameters length compact context data
  rw [← same] at estimate
  rw [originalHomogeneousDatumNorm_eq_incoming parameters length compact context.lower context.positive context.lowerHalf
    context.lengthPositive context.state data candidate
    (originalBoundaryTrace_of_equation parameters length compact context.lower context.positive context.lowerHalf context.lengthPositive
      context.state context.widthHalf context.widthLength context.small data candidate equation) sources outer] at estimate
  exact estimate

end Grad.AnnularWeightedUniqueness
