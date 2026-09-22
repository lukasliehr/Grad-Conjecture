import AKEH1OriginalSourceNormPacket
import AKDV14ActualSameCoreCurrent

noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 900000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.OriginalMainConsumer
open Grad.ActualPuncturedFamily Grad.Constraints Grad.Q24Realization Grad.AxisSplit Grad.ChartAxisLift Grad.ConstrainedTransfer Grad.NonlinearQuotientBounds
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




open Grad.ActualScaledNativeCoefficients Grad.ActualCartesianDescent Grad.OriginalCartesianTameEstimate
open Grad.ActualCartesianWeakEquations Grad.ActualScalarWeakEquations Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.SourceBoundaryTrace Grad.ActualCartesianFlux Grad.ActualNativeCellMoments
open Grad.SourceCollarCoefficients Grad.CartesianStartup Grad.ActualSmoothPhysicalField Grad.ActualPuncturedReconstruction
open Grad.NonlinearProduct


open Grad.RealFixedRanges Grad.PhysicalCoordinates Grad.NashMoser.OriginalIteration
open Grad.NashMoser.OriginalLimit Grad.OriginalInverseNeighborhood Grad.FinitePhysicalJetLift

open Grad.ActualOriginalSourceMoments
variable {parameters : PhaseParameters} {positive : 0 < parameters.length}
  {reference : Seed.Parameters} {inside : reference ∈ Seed.parameterDomain} {center : Seed.Parameters}
  (product : OriginalPhysicalProduct parameters positive reference inside center)
  (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*parameters.length))
  (higher : ℕ) (higherLarge : 24 ≤ higher)
  (finite : OriginalFiniteParameter) (member : finite ∈ product.neighborhood.parameterDomain)
  (state : stateSmoothRange parameters reference inside)
  (low : stateSize parameters reference inside higher 0 state ≤ 2*product.neighborhood.radius)
  (source : OriginalFlatSource parameters parameters.length)

/-- The literal residual already used by the canonical native recovery. -/
def actualProductResidual : SmoothQuotient parameters :=
  actualFiniteSourceResidual parameters parameters.length (finite.1 0) reference inside finite.1
    (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state)
    (actualJetExhaustion_cubicSmall parameters parameters.length product.coefficientBound reference inside finite.1
      (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state)
      (actualProduct_recovery_smallness product higher higherLarge finite member state low).1) source

/-- A norm packet for the SAME canonical compact core and actual residual.
The coefficient is retained literally, so the physical unit constructor can be used directly. -/
def actualProductNormPacket {radius : ℝ} (coefficient : OriginalUnitRankState parameters parameters.length radius) :
    StartupOriginalUnitNormPacket parameters parameters.length radius :=
  originalSourceNormPacket coefficient
    (canonicalProductCompactCore product widthHalf widthLength higher higherLarge finite member state low source)
    (actualProductResidual product higher higherLarge finite member state low source)

theorem actualProductNormPacket_core {radius : ℝ} (coefficient : OriginalUnitRankState parameters parameters.length radius) :
    (actualProductNormPacket product widthHalf widthLength higher higherLarge finite member state low source coefficient).core=
      canonicalProductCompactCore product widthHalf widthLength higher higherLarge finite member state low source := rfl

theorem actualProductNormPacket_coefficient {radius : ℝ} (coefficient : OriginalUnitRankState parameters parameters.length radius) :
    (actualProductNormPacket product widthHalf widthLength higher higherLarge finite member state low source coefficient).coefficient=coefficient := rfl

end Grad.OriginalMainConsumer
