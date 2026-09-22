import AKEH9ActualFullPlanarAssembly
import AKEF8ActualPrincipalCompactData

noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 900000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology ContDiff
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

open Grad.PDEBootstrap Grad.GenericCarriers
open Grad.ActualOriginalSourceMoments
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.WeightedJets.ZeroExtension
variable (parameters : PhaseParameters) (positive : 0<parameters.length)
  (reference : Seed.Parameters) (inside : reference∈Seed.parameterDomain)
  (center : Seed.Parameters) (insideC : center∈Seed.parameterDomain) (zeroC : center 0=0)
  (widthHalf : parameters.gamma≤1/2) (widthLength : parameters.gamma≤Real.sqrt 5/(6*parameters.length))
  (higher : ℕ) (higherLarge : 24≤higher)

/-- The actual native compact equation discharges the complete inner norm
estimate. Every constant precedes the actual finite input and source. -/
theorem actualPrincipal_insideEstimate :
    ActualPrincipalInsideEstimate parameters positive reference inside center insideC zeroC
      widthHalf widthLength higher higherLarge := by
  intro rank epsilon epsilonPositive
  let packets := ActualPrincipalNormState.packet parameters positive reference inside center insideC zeroC
    higher higherLarge widthHalf widthLength
  let certificate := fun datum : ActualPrincipalNormState parameters positive reference inside center insideC zeroC higher =>
    actualPrincipal_compactData parameters positive reference inside center insideC zeroC
      actualNativeOuterCutoff actualNativeOuterCutoff_smooth actualNativeOuterCutoff_compact
      widthHalf widthLength higher higherLarge datum.val.1 datum.property.1 datum.val.2.1 datum.property.2 datum.val.2.2
      actualNativeInsideCutoff actualNativeInsideCutoff_smooth actualNativeInsideCutoff_compact (rank+2)
  let data := fun datum => (certificate datum).choose
  have radiusNonnegative : 0≤1+‖center‖ := by positivity
  exact StartupOriginalUnitNormPacket.actualCompact_planar_bound parameters parameters.length (1+‖center‖)
    radiusNonnegative rank parameters.length⁻¹ packets
    actualNativeInsideCutoff actualNativeInsideCutoff_smooth actualNativeInsideCutoff_compact
    actualNativeInsideCutoff_radial actualInsideNormLocalizer
    actualNativeOuterCutoff actualNativeOuterCutoff_smooth actualNativeOuterCutoff_compact
    (fun _ present => actualNativeCutoff_plateau present)
    (ActualPrincipalNormState.small parameters positive reference inside center insideC zeroC
      higher higherLarge widthHalf widthLength)
    data (fun datum => (certificate datum).choose_spec.1)
    (fun datum => (certificate datum).choose_spec.2.2.1)
    (fun datum => (certificate datum).choose_spec.2.1)
    (fun datum => (certificate datum).choose_spec.2.2.2) epsilon epsilonPositive

/-- The literal full original planar estimate has no remaining analytic
hypothesis: SAME canonical solve, one fixed product, all ranks at least two. -/
def actualPrincipal_compactPlanarEstimate :
    ActualProductCompactPlanarEstimate
      (actualPrincipalProduct parameters positive reference inside center insideC zeroC
        actualNativeOuterCutoff actualNativeOuterCutoff_smooth actualNativeOuterCutoff_compact)
      widthHalf widthLength higher higherLarge 0 :=
  actualPrincipalPlanar_of_inside parameters positive reference inside center insideC zeroC
    widthHalf widthLength higher higherLarge
    (actualPrincipal_insideEstimate parameters positive reference inside center insideC zeroC
      widthHalf widthLength higher higherLarge)

end Grad.OriginalMainConsumer
