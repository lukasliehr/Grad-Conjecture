import AKDV11ActualCompactHighRankAbsorption
import AKDV4ActualFlatSolveToNewton

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

variable {parameters : PhaseParameters} {positive : 0<parameters.length}
  {reference : Seed.Parameters} {inside : reference∈Seed.parameterDomain} {center : Seed.Parameters}
  (product : OriginalPhysicalProduct parameters positive reference inside center)
  (widthHalf : parameters.gamma≤1/2) (widthLength : parameters.gamma≤Real.sqrt 5/(6*parameters.length))
  (higher : ℕ) (higherLarge : 24≤higher) (loss : ℕ) (lossLarge : 20≤loss)
  (estimate : ActualProductCompactOneHigh product widthHalf widthLength higher higherLarge loss)
  (radius : ℝ) (radiusNonnegative : 0≤radius)
  (units : ∀ finite (_member : finite∈product.neighborhood.parameterDomain)
    (state : stateSmoothRange parameters reference inside)
    (_low : stateSize parameters reference inside higher 0 state≤2*product.neighborhood.radius),
    OriginalUnitRankState parameters parameters.length radius)
  (sameBudget : ∀ finite member state low grade,
    physicalBudget parameters (units finite member state low).field
      (units finite member state low).rho (units finite member state low).epsilon grade =
    physicalBudget parameters (actualFiniteCurrentField parameters reference inside finite.1
      (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state))
      (finite.1 0) finite.2 grade)
  (sameCurrent : ∀ finite member state low (source : OriginalFlatSource parameters parameters.length),
    let unit := units finite member state low
    originalSourceFieldLinear parameters
      (canonicalProductRecovery product widthHalf widthLength higher higherLarge finite member state low source).covariant =
    originalCurrentKernel (unitDiskAdmissible parameters) unit.data.gaugeDeviation
      (unit.coherent radiusNonnegative).2.2.2.1 (unit.inverseCoherent radiusNonnegative)
      (originalSourceFieldLinear parameters
        (canonicalProductCompactCore product widthHalf widthLength higher higherLarge finite member state low source)))

/-- Typed current transfer, keeping the product opaque while transporting
only its literal scalar budget. The actual product supplies both identities. -/
def productCovariantOneHigh_of_compact :
    ActualProductCovariantOneHigh product widthHalf widthLength higher higherLarge loss where
  constant := (originalUnitCurrent_oneHigh_of_compact parameters parameters.length radius radiusNonnegative
    loss lossLarge estimate.constant estimate.nonnegative
    (productCompactCellConstant parameters positive product.coefficientBound 0)
    (productCompactCellConstant_nonnegative parameters positive product.coefficientBound 0)).choose
  nonnegative := (originalUnitCurrent_oneHigh_of_compact parameters parameters.length radius radiusNonnegative
    loss lossLarge estimate.constant estimate.nonnegative
    (productCompactCellConstant parameters positive product.coefficientBound 0)
    (productCompactCellConstant_nonnegative parameters positive product.coefficientBound 0)).choose_spec.1
  bounded := by
    intro finite member state low source grade
    let unit := units finite member state low
    have budgetEq := sameBudget finite member state low
    have unitBound : physicalBudget parameters unit.field unit.rho unit.epsilon 20≤1 := by
      rw [budgetEq]
      exact (actualProduct_recovery_smallness product higher higherLarge finite member state low).2.1
    have cell := canonicalProductCompactCore_cellBound product widthHalf widthLength higher higherLarge finite member state low source 0
    simp only [Nat.zero_add] at cell
    rw [←budgetEq 20] at cell
    have compactPaid (order : ℕ) :
        originalGradeNorm (parameters := parameters) order
          (canonicalProductCompactCore product widthHalf widthLength higher higherLarge finite member state low source)≤
        estimate.constant order*(‖quotientEta parameters (order+loss) source.val.val‖+
          physicalBudget parameters unit.field unit.rho unit.epsilon (order+loss)*‖quotientEta parameters loss source.val.val‖) :=
      (estimate.bounded finite member state low source order).trans_eq (congrArg
        (fun budget : ℝ => estimate.constant order*(‖quotientEta parameters (order+loss) source.val.val‖+
          budget*‖quotientEta parameters loss source.val.val‖)) (budgetEq (order+loss)).symm)
    have bounded := (originalUnitCurrent_oneHigh_of_compact parameters parameters.length radius radiusNonnegative
      loss lossLarge estimate.constant estimate.nonnegative
      (productCompactCellConstant parameters positive product.coefficientBound 0)
      (productCompactCellConstant_nonnegative parameters positive product.coefficientBound 0)).choose_spec.2
      unit source.val.val
      (canonicalProductCompactCore product widthHalf widthLength higher higherLarge finite member state low source)
      (canonicalProductRecovery product widthHalf widthLength higher higherLarge finite member state low source).covariant
      unitBound cell compactPaid (sameCurrent finite member state low source) grade
    exact bounded.trans_eq (congrArg
      (fun budget : ℝ => _*(‖quotientEta parameters (grade+loss) source.val.val‖+
        budget*‖quotientEta parameters loss source.val.val‖)) (budgetEq (grade+loss)))

end Grad.OriginalMainConsumer
