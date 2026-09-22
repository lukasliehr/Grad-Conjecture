import AKT18ActualCartesianSourcePhysicalConsumer
import AJG14SamePhysicalInverseConsumer
import AKG11FullOriginalPacketAndRowLocality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.ActualPuncturedReconstruction
open Grad.CartesianState Grad.AnnularFullGraph Grad.AnnularForwardDatum Grad.AnnularStrongOrbit
open Grad.AnnularForwardTraces Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularRestriction
open Grad.AnnularExhaustionEstimate Grad.AnnularWeakExhaustion Grad.AnnularFullSource
open Grad.AnnularHighGenerators Grad.AnnularCrossOrbit Grad.ActualAnnularExhaustion
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.SourceCollarFullSource Grad.ExhaustionSourceAllocation
open Grad.GaugeCoefficients.Physical.Allocation
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule
  sourceRadialRealInner sourceGraphRealInner sourceKnownGraphRealInner
  weakRetainedRealInner weakSourcesRealInner weakFiveRealInner

attribute [local instance] weakWeightedRetainedRealInner
attribute [local instance] Grad.AnnularStrongOrbit.knownAmbientNormed Grad.AnnularStrongOrbit.knownAmbientSeminormed Grad.AnnularStrongOrbit.knownAmbientRealNormed Grad.AnnularStrongOrbit.knownAmbientRealModule
  Grad.AnnularStrongOrbit.strongCarrierNormed Grad.AnnularStrongOrbit.strongCarrierSeminormed Grad.AnnularStrongOrbit.strongCarrierRealNormed Grad.AnnularStrongOrbit.strongCarrierRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace
  Grad.AnnularCrossOrbit.coupledNormed Grad.AnnularCrossOrbit.coupledSeminormed
  Grad.AnnularCrossOrbit.coupledComplexNormed Grad.AnnularCrossOrbit.coupledComplexModule
  Grad.AnnularCrossOrbit.coupledRealNormed Grad.AnnularCrossOrbit.coupledRealModule
  Grad.AnnularCrossOrbit.coupledOperatorRealNormed Grad.AnnularCrossOrbit.coupledOperatorRealModule





open Grad.AnnularPhysicalReconstruction Grad.AnnularKernelL2 Grad.SourceCollarDivision

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)

/-- The actual complete covariant, reconstructed from the original full
source datum and the SAME retained part of the full graph. -/
def originalGraphCovariant (data : OriginalStrongCarrier parameters lower 0 0)
    (point : OriginalFiveBlockAmbient parameters lower length positive) : DivisionRow 3 lower :=
  fullCovariantAction parameters length compact lower positive bounded state.val
    (originalSevenPacket parameters lower length positive bounded lengthPositive data point.ofLp.1)

/-- The genuine angular derivative from the SAME seven-slot reconstruction. -/
def originalGraphRotatedCovariant (data : OriginalStrongCarrier parameters lower 0 0)
    (point : OriginalFiveBlockAmbient parameters lower length positive) : DivisionRow 3 lower :=
  fullRotatedCovariantAction parameters length compact lower positive bounded state.val
    (originalSevenPacket parameters lower length positive bounded lengthPositive data point.ofLp.1)

theorem originalGraphCovariant_shared (data : OriginalStrongCarrier parameters lower 0 0)
    (point : OriginalFiveBlockAmbient parameters lower length positive) :
    originalGraphCovariant parameters length compact lower positive bounded lengthPositive state data point =
      sharedFullCovariant parameters length compact lower positive bounded lengthPositive state.val
        (originalWeightedDatum parameters lower length positive bounded lengthPositive data)
        (originalWeightedRetainedObservation parameters lower length positive bounded lengthPositive point) := rfl

theorem originalGraphRotatedCovariant_shared (data : OriginalStrongCarrier parameters lower 0 0)
    (point : OriginalFiveBlockAmbient parameters lower length positive) :
    originalGraphRotatedCovariant parameters length compact lower positive bounded lengthPositive state data point =
      sharedFullRotatedCovariant parameters length compact lower positive bounded lengthPositive state.val
        (originalWeightedDatum parameters lower length positive bounded lengthPositive data)
        (originalWeightedRetainedObservation parameters lower length positive bounded lengthPositive point) := rfl

end Grad.ActualPuncturedReconstruction
