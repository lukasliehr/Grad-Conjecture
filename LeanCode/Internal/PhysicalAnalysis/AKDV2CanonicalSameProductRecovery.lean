import AKDV20NativeRecoveryPacket
import AKDV26ActualJetResidualNativeRecovery

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

/-- The sharper residual constant is fixed before the product point and source. -/
def productRecoveryResidualNativeConstant (parameters : PhaseParameters) (positive : 0 < parameters.length)
    (compact : ℝ) : ℕ → ℝ :=
  (actualFiniteJet_fullRecovery_withResidualNative parameters parameters.length compact positive).choose

theorem productRecoveryResidualNativeConstant_nonnegative (parameters : PhaseParameters)
    (positive : 0 < parameters.length) (compact : ℝ) (grade : ℕ) :
    0 ≤ productRecoveryResidualNativeConstant parameters positive compact grade :=
  (actualFiniteJet_fullRecovery_withResidualNative parameters parameters.length compact positive).choose_spec.1 grade

/-- The native and cell constants are fixed before the product point and source. -/
def productRecoveryNativeConstant (parameters : PhaseParameters) (positive : 0 < parameters.length)
    (compact : ℝ) : ℕ → ℝ :=
  (actualFiniteJet_fullRecovery_withResidualNative parameters parameters.length compact positive).choose_spec.2.choose

def productRecoveryCellConstant (parameters : PhaseParameters) (positive : 0 < parameters.length)
    (compact : ℝ) : ℕ → ℝ :=
  (actualFiniteJet_fullRecovery_withResidualNative parameters parameters.length compact positive).choose_spec.2.choose_spec.choose

def productRecoveryBaseConstant (parameters : PhaseParameters) (positive : 0 < parameters.length)
    (compact : ℝ) : ℝ :=
  (actualFiniteJet_fullRecovery_withResidualNative parameters parameters.length compact positive).choose_spec.2.choose_spec.choose_spec.2.2.choose

theorem productRecoveryNativeConstant_nonnegative (parameters : PhaseParameters)
    (positive : 0 < parameters.length) (compact : ℝ) (grade : ℕ) :
    0 ≤ productRecoveryNativeConstant parameters positive compact grade :=
  (actualFiniteJet_fullRecovery_withResidualNative parameters parameters.length compact positive).choose_spec.2.choose_spec.choose_spec.1 grade

theorem productRecoveryCellConstant_nonnegative (parameters : PhaseParameters)
    (positive : 0 < parameters.length) (compact : ℝ) (grade : ℕ) :
    0 ≤ productRecoveryCellConstant parameters positive compact grade :=
  (actualFiniteJet_fullRecovery_withResidualNative parameters parameters.length compact positive).choose_spec.2.choose_spec.choose_spec.2.1 grade

variable {parameters : PhaseParameters} {positive : 0 < parameters.length}
  {reference : Seed.Parameters} {inside : reference ∈ Seed.parameterDomain} {center : Seed.Parameters}
  (product : OriginalPhysicalProduct parameters positive reference inside center)
  (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*parameters.length))
  (higher : ℕ) (higherLarge : 24 ≤ higher)
  (finite : OriginalFiniteParameter) (member : finite ∈ product.neighborhood.parameterDomain)
  (state : stateSmoothRange parameters reference inside)
  (low : stateSize parameters reference inside higher 0 state ≤ 2*product.neighborhood.radius)
  (source : OriginalFlatSource parameters parameters.length)

local notation "seedInside" => product.neighborhood.patchInside (product.neighborhood.seedInside finite member)
local notation "field" => actualFiniteCurrentField parameters reference inside finite.1 seedInside (finite.2,state)
local notation "jetSmall" => (actualProduct_recovery_smallness product higher higherLarge finite member state low).1
local notation "currentLow" => actualJetExhaustion_cubicSmall parameters parameters.length product.coefficientBound
  reference inside finite.1 seedInside (finite.2,state) jetSmall
local notation "nativeState" => actualJetExhaustionState parameters parameters.length product.coefficientBound
  reference inside finite.1 seedInside (finite.2,state) jetSmall product.nonnegative
  (product.seedBound finite member 1) (product.seedBound finite member 2) (product.seedBound finite member 3)
local notation "nativeSmall" => actualJetExhaustion_exSmall parameters parameters.length product.coefficientBound
  reference inside finite.1 seedInside (finite.2,state) jetSmall
local notation "residual" => actualFiniteSourceResidual parameters parameters.length (finite.1 0)
  reference inside finite.1 seedInside (finite.2,state) currentLow source
local notation "residualFlat" => actualFiniteSourceResidual_isFlat parameters parameters.length (finite.1 0) positive
  reference inside finite.1 seedInside (finite.2,state) currentLow
  ((product.neighborhood.raiseBase higher higherLarge).axis state low) source

/-- One SAME native family and its original physical cores, with the actual
finite-source, native, cell and recovery identities already discharged. -/
abbrev ActualProductRecovery :=
  NativeRecoveryPacket parameters parameters.length product.coefficientBound positive widthHalf widthLength
    nativeState nativeSmall residual residualFlat source.val.val
    (productRecoveryNativeConstant parameters positive product.coefficientBound)
    (productRecoveryCellConstant parameters positive product.coefficientBound)
    (productRecoveryBaseConstant parameters positive product.coefficientBound)
    (productRecoveryResidualNativeConstant parameters positive product.coefficientBound)

/-- The packet is constructed from DS22 with both residual and full-source estimates on the actual product. No native
regularity, derivative, source-fidelity or cell estimate is assumed here. -/
theorem actualProductRecovery_nonempty :
    Nonempty (ActualProductRecovery product widthHalf widthLength higher higherLarge finite member state low source) := by
  have certificate := (actualFiniteJet_fullRecovery_withResidualNative parameters parameters.length product.coefficientBound positive).choose_spec.2
  have solve := certificate.choose_spec.choose_spec.2.2.choose_spec.2
  have smallness := actualProduct_recovery_smallness product higher higherLarge finite member state low
  let solved := solve widthHalf widthLength reference inside finite.1 seedInside (finite.2,state)
    ((product.neighborhood.raiseBase higher higherLarge).axis state low) product.nonnegative
    (product.seedBound finite member 1) (product.seedBound finite member 2) (product.seedBound finite member 3)
    smallness.1 smallness.2.1 smallness.2.2 source
  exact ⟨⟨solved.choose, solved.choose_spec⟩⟩

/-- The canonical packet fixes one SAME original covariant/U/Xi/S solve. -/
def canonicalProductRecovery :
    ActualProductRecovery product widthHalf widthLength higher higherLarge finite member state low source :=
  Classical.choice (actualProductRecovery_nonempty product widthHalf widthLength higher higherLarge finite member state low source)

end Grad.OriginalMainConsumer
