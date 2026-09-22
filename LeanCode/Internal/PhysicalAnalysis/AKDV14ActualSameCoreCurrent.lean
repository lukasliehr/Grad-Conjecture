import AKDV13ActualUnitBudgetFidelity
import AKDV16NativeUnitCurrentPacket
import AKDS34OriginalUnitLedgerFidelity

noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1800000
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




open Grad.GaugeCoefficients.Physical.RadialLedger
attribute [local irreducible] canonicalProductRecovery NativeRecoveryPacket.family
  NativeRecoveryPacket.covariant NativeRecoveryPacket.vector NativeRecoveryPacket.scalar actualFiniteCurrentField

attribute [local irreducible] canonicalProductCompactCore

open Grad.PDEBootstrap
variable (parameters : PhaseParameters) (positive : 0 < parameters.length)
  (reference : Seed.Parameters) (inside : reference ∈ Seed.parameterDomain)
  (center : Seed.Parameters) (insideC : center ∈ Seed.parameterDomain) (zeroC : center 0=0)
  (outer : Spatial → ℝ) (smooth : ContDiff ℝ ∞ outer) (compact : HasCompactSupport outer)
  (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*parameters.length))
  (higher : ℕ) (higherLarge : 24 ≤ higher)

local notation "principalProduct" => actualPrincipalProduct parameters positive reference inside center insideC zeroC outer smooth compact

/-- The original native equations recover the SAME canonical covariant
core through the faithful physical-length current. No current identity is
assumed of the actual solve. -/
theorem actualPrincipalCompactCurrent :
    ActualPrincipalCompactCurrent parameters positive reference inside center insideC zeroC outer smooth compact
      widthHalf widthLength higher higherLarge := by
  intro finite member state low source
  let unit := actualPrincipalUnitState parameters positive reference inside center insideC zeroC outer smooth compact
    higher higherLarge finite member state low
  let packet := canonicalProductRecovery principalProduct widthHalf widthLength higher higherLarge finite member state low source
  have radiusNonnegative : 0≤1+‖center‖ := by positivity
  exact (packet.originalUnit_current (1+‖center‖) radiusNonnegative unit rfl
    (canonicalProductCompactCore principalProduct widthHalf widthLength higher higherLarge finite member state low source)
    (canonicalProductCompactCore_sameCircle principalProduct widthHalf widthLength higher higherLarge finite member state low source)).symm

end Grad.OriginalMainConsumer
