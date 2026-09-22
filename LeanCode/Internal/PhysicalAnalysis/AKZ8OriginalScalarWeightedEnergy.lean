import AKZ6SamePhysicalVectorRecovery
import AKZ7SamePhysicalScalarOverRadius

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.ActualPhysicalField
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





open Grad.AnnularKernelContinuity
open Grad.AnnularPhysicalReconstruction Grad.AnnularKernelL2 Grad.SourceCollarDivision


open Grad.ActualPuncturedReconstruction Grad.AnnularCurrentEnergy

variable (parameters : PhaseParameters) (length lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (data : OriginalStrongCarrier parameters lower 0 0)
    (point : OriginalFiveBlockAmbient parameters lower length positive)

/-- The actual S/r coordinate, extracted from the same original seven-input
packet. Its physical coefficient identification is AKZ7. -/
def originalScalarOverRadius : DivisionRow 1 lower :=
  bulkMatrixUnit lower (0 : Fin 1) (3 : Fin 7)
    (originalSevenPacket parameters lower length positive bounded lengthPositive data point.ofLp.1)

theorem originalSevenPacket_weightedBound :
    ‖originalSevenPacket parameters lower length positive bounded lengthPositive data point.ofLp.1‖ ≤
      (11 + 4 * length) * originalWeightedRetainedNorm parameters lower length positive bounded lengthPositive point.ofLp.1 +
        3 * originalWeightedDatumNorm parameters lower length positive bounded lengthPositive data := by
  have actual := fullStrongSevenInput_bound parameters length lower lengthPositive positive bounded
    (originalWeightedDatum parameters lower length positive bounded lengthPositive data)
    (originalWeightedRetainedObservation parameters lower length positive bounded lengthPositive point)
  have retainedNorm : ‖originalWeightedRetainedObservation parameters lower length positive bounded lengthPositive point‖ =
      originalWeightedRetainedNorm parameters lower length positive bounded lengthPositive point.ofLp.1 := rfl
  have datumNorm : ‖originalWeightedDatum parameters lower length positive bounded lengthPositive data‖ =
      originalWeightedDatumNorm parameters lower length positive bounded lengthPositive data := rfl
  have payment := congrArg₂ (fun retained datum : ℝ => (11 + 4 * length) * retained + 3 * datum) retainedNorm datumNorm
  have samePacket : ‖originalSevenPacket parameters lower length positive bounded lengthPositive data point.ofLp.1‖ =
      ‖fullStrongSevenInput parameters length lower lengthPositive positive bounded
        (originalWeightedDatum parameters lower length positive bounded lengthPositive data)
        (originalWeightedRetainedObservation parameters lower length positive bounded lengthPositive point)‖ := rfl
  linarith only [actual,payment,samePacket]

theorem originalScalarOverRadius_bound :
    ‖originalScalarOverRadius parameters length lower positive bounded lengthPositive data point‖ ≤
      (11 + 4 * length) * originalWeightedRetainedNorm parameters lower length positive bounded lengthPositive point.ofLp.1 +
        3 * originalWeightedDatumNorm parameters lower length positive bounded lengthPositive data :=
  (bulkMatrixUnit_bound lower (0 : Fin 1) (3 : Fin 7) _).trans
    (originalSevenPacket_weightedBound parameters length lower positive bounded lengthPositive data point)

end Grad.ActualPhysicalField
