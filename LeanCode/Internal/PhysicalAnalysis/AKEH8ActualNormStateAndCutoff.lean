import AKEH5ActualPrincipalNormPacket
import AKDW32ActualCompactPlanarEstimate
import AKCX59FixedNativeRadialCutoffs
import ZE1Compact

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
open Grad.WeightedJets.ZeroExtension

/-- The chosen inside cutoff has its actual compact-support localizer. -/
def actualInsideNormLocalizer : TestLocalizer openUnitDisk (tsupport actualNativeInsideCutoff) :=
  compactLocalizer openUnitDisk (tsupport actualNativeInsideCutoff) actualNativeInsideCutoff_compact openUnitDisk_isOpen (by
    intro point present
    apply actualNativeOuterCutoff_inside
    apply subset_tsupport
    intro zero
    have one := actualNativeCutoff_plateau present
    rw [zero] at one
    norm_num at one)

variable (parameters : PhaseParameters) (positive : 0<parameters.length)
  (reference : Seed.Parameters) (inside : reference∈Seed.parameterDomain)
  (center : Seed.Parameters) (insideC : center∈Seed.parameterDomain) (zeroC : center 0=0)
  (higher : ℕ) (higherLarge : 24≤higher)

/-- All finite inputs in the one fixed original product, packaged before
any estimate constant is selected. -/
def ActualPrincipalNormState :=
  {datum : OriginalFiniteParameter×stateSmoothRange parameters reference inside×OriginalFlatSource parameters parameters.length //
    datum.1∈(actualPrincipalProduct parameters positive reference inside center insideC zeroC
      actualNativeOuterCutoff actualNativeOuterCutoff_smooth actualNativeOuterCutoff_compact).neighborhood.parameterDomain ∧
    stateSize parameters reference inside higher 0 datum.2.1≤
      2*(actualPrincipalProduct parameters positive reference inside center insideC zeroC
        actualNativeOuterCutoff actualNativeOuterCutoff_smooth actualNativeOuterCutoff_compact).neighborhood.radius}

namespace ActualPrincipalNormState
variable (widthHalf : parameters.gamma≤1/2) (widthLength : parameters.gamma≤Real.sqrt 5/(6*parameters.length))

def packet (datum : ActualPrincipalNormState parameters positive reference inside center insideC zeroC higher) :
    StartupOriginalUnitNormPacket parameters parameters.length (1+‖center‖) :=
  actualPrincipalNormPacket parameters positive reference inside center insideC zeroC
    actualNativeOuterCutoff actualNativeOuterCutoff_smooth actualNativeOuterCutoff_compact
    widthHalf widthLength higher higherLarge datum.val.1 datum.property.1 datum.val.2.1 datum.property.2 datum.val.2.2

/-- The principal radius is fixed before the bundled input and every rank. -/
theorem small (datum : ActualPrincipalNormState parameters positive reference inside center insideC zeroC higher) :
    let unit := (packet parameters positive reference inside center insideC zeroC higher higherLarge widthHalf widthLength datum).coefficient;
    physicalBudget parameters unit.field unit.rho unit.epsilon 10<
      originalUnitPrincipalRadius parameters parameters.length (1+‖center‖)
        actualNativeOuterCutoff actualNativeOuterCutoff_smooth actualNativeOuterCutoff_compact := by
  let product := actualPrincipalProduct parameters positive reference inside center insideC zeroC
    actualNativeOuterCutoff actualNativeOuterCutoff_smooth actualNativeOuterCutoff_compact
  let unit := actualPrincipalUnitState parameters positive reference inside center insideC zeroC
    actualNativeOuterCutoff actualNativeOuterCutoff_smooth actualNativeOuterCutoff_compact
    higher higherLarge datum.val.1 datum.property.1 datum.val.2.1 datum.property.2
  have low24 := product.neighborhood.raiseBase_low higher higherLarge datum.val.2.1 datum.property.2
  have below := actualOriginalProductBelow_budget parameters positive reference inside center insideC zeroC
    (originalUnitPrincipalRadius parameters parameters.length (1+‖center‖) actualNativeOuterCutoff actualNativeOuterCutoff_smooth actualNativeOuterCutoff_compact)
    (originalUnitPrincipalRadius_positive parameters parameters.length (1+‖center‖) actualNativeOuterCutoff actualNativeOuterCutoff_smooth actualNativeOuterCutoff_compact)
    datum.val.1 datum.property.1 datum.val.2.1 low24
  exact (physicalBudget_monotone parameters unit.field unit.rho unit.epsilon (by norm_num : 10≤24)).trans_lt below

end ActualPrincipalNormState
end Grad.OriginalMainConsumer
