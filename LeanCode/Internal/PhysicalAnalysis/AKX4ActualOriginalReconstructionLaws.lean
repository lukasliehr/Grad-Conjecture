import AKX3SamePhysicalReconstructionLocality

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


open Set Filter MeasureTheory
open scoped ENNReal Topology
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction

/-- Original force rows, the genuine angular derivative, both gauges and
corrected flux hold for the SAME reconstruction of the original graph/data. -/
theorem originalGraphCovariants_physicalLaws
    (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (data : OriginalStrongCarrier parameters lower 0 0)
    (point : OriginalFiveBlockAmbient parameters lower length positive) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      let radial := collarRadius lower positive bounded radius
      let input := physicalBulkSevenTrace parameters lower positive radial
        (collectRadial lower (originalSevenPacket parameters lower length positive bounded lengthPositive data point.ofLp.1) radius)
      let covariant := originalPhysicalSlice parameters lower positive bounded
        (originalGraphCovariant parameters length compact lower positive bounded lengthPositive state data point) radius
      let rotated := originalPhysicalSlice parameters lower positive bounded
        (originalGraphRotatedCovariant parameters length compact lower positive bounded lengthPositive state data point) radius
      OriginalSliceLaws parameters length compact state.val radial input covariant rotated ∧
        radialCorrectedFluxTrace parameters length compact state.val.val radial 0 0 covariant (input 3) =
          physicalBulkFlux parameters lower positive radial
            (collectRadial lower (originalSevenPacket parameters lower length positive bounded lengthPositive data point.ofLp.1) radius) := by
  dsimp only
  exact (sharedFull_originalSliceLaws parameters length compact lower positive bounded lengthPositive state.val
    (originalWeightedDatum parameters lower length positive bounded lengthPositive data)
    (originalWeightedRetainedObservation parameters lower length positive bounded lengthPositive point)).and
    (sharedFull_originalCorrectedFlux parameters length compact lower positive bounded lengthPositive state.val
      (originalWeightedDatum parameters lower length positive bounded lengthPositive data)
      (originalWeightedRetainedObservation parameters lower length positive bounded lengthPositive point))

end Grad.ActualPuncturedReconstruction
