import AKX1SameOriginalGraphCovariants

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





open Grad.AnnularKernelContinuity
open Grad.AnnularPhysicalReconstruction Grad.AnnularKernelL2 Grad.SourceCollarDivision


variable (parameters : PhaseParameters) (length compact lower upper : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (state : RetainedInverseState parameters length compact)
    (data : OriginalStrongCarrier parameters lower 0 0) (targetData : OriginalStrongCarrier parameters upper 0 0)
    (sameSources : targetData.val.ofLp.1 = originalFullSourceRestriction parameters lower upper included data.val.ofLp.1)
    (point : OriginalFiveBlockAmbient parameters lower length lowerPositive)
    (target : OriginalFiveBlockAmbient parameters upper length upperPositive)
    (compatible : originalFiveBlockRestriction parameters lower upper length lowerPositive upperPositive upperBounded
      lengthPositive included point = target)

include compatible sameSources

theorem originalSevenPacket_family_restriction :
    originalBulkRestriction 7 lower upper included
      (originalSevenPacket parameters lower length lowerPositive (included.trans upperBounded.le) lengthPositive data point.ofLp.1) =
    originalSevenPacket parameters upper length upperPositive upperBounded.le lengthPositive targetData target.ofLp.1 := by
  have coordinate := (originalFiveBlockRestriction_coordinates parameters lower upper length lowerPositive upperPositive
    upperBounded lengthPositive included point).1
  have retained := coordinate.symm.trans (congrArg (fun item : OriginalFiveBlockAmbient parameters upper length upperPositive => item.ofLp.1) compatible)
  exact (originalSevenPacket_restriction_of_sources parameters lower upper length lowerPositive upperPositive upperBounded
    lengthPositive included data targetData sameSources point.ofLp.1).trans
    (congrArg (originalSevenPacket parameters upper length upperPositive upperBounded.le lengthPositive targetData) retained)

/-- Both actual physical reconstructed fields are compatible under genuine
endpoint-changing restriction, using the same source4 and retained graph. -/
theorem originalGraphCovariants_restriction :
    originalBulkRestriction 3 lower upper included
      (originalGraphCovariant parameters length compact lower lowerPositive (included.trans upperBounded.le) lengthPositive state data point) =
      originalGraphCovariant parameters length compact upper upperPositive upperBounded.le lengthPositive state targetData target ∧
    originalBulkRestriction 3 lower upper included
      (originalGraphRotatedCovariant parameters length compact lower lowerPositive (included.trans upperBounded.le) lengthPositive state data point) =
      originalGraphRotatedCovariant parameters length compact upper upperPositive upperBounded.le lengthPositive state targetData target := by
  have packet := originalSevenPacket_family_restriction parameters length lower upper lowerPositive upperPositive upperBounded
    lengthPositive included data targetData sameSources point target compatible
  constructor
  · exact (originalBulkRestriction_regularRadialBulkAction parameters 0 lower upper included lowerPositive upperPositive upperBounded.le
      (fun radius => radialNormalizedCovariantKernel parameters length compact state.val.val radius state.val.property)
      (radialNormalizedCovariantKernel_regular parameters length compact state.val) _).trans
      (congrArg (fullCovariantAction parameters length compact upper upperPositive upperBounded.le state.val) packet)
  · exact (originalBulkRestriction_regularRadialBulkAction parameters 0 lower upper included lowerPositive upperPositive upperBounded.le
      (fun radius => radialNormalizedRotatedCovariantKernel parameters length compact state.val.val radius state.val.property)
      (radialNormalizedRotatedCovariantKernel_regular parameters length compact state.val) _).trans
      (congrArg (fullRotatedCovariantAction parameters length compact upper upperPositive upperBounded.le state.val) packet)

end Grad.ActualPuncturedReconstruction
