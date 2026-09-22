import AKDV2CanonicalSameProductRecovery

noncomputable section
set_option autoImplicit false
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


variable {parameters : PhaseParameters} {positive : 0 < parameters.length}
  {reference : Seed.Parameters} {inside : reference ∈ Seed.parameterDomain} {center : Seed.Parameters}
  (product : OriginalPhysicalProduct parameters positive reference inside center)
  (loss : ℕ) (lossLarge : 20 ≤ loss)
  (covariantConstant : ℕ → ℝ) (covariantNonnegative : ∀ grade, 0 ≤ covariantConstant grade)

/-- The pair constant depends only on the fixed product and the covariant
constant, before any finite parameter, state or source is supplied. -/
def actualProductPairConstant (grade : ℕ) : ℝ :=
  (finiteJetPair_oneHigh_payment parameters parameters.length grade loss lossLarge
    (covariantConstant grade) (productRecoveryCellConstant parameters positive product.coefficientBound 0)
    (covariantNonnegative grade)
    (productRecoveryCellConstant_nonnegative parameters positive product.coefficientBound 0)).choose

theorem actualProductPairConstant_nonnegative (grade : ℕ) :
    0 ≤ actualProductPairConstant product loss lossLarge covariantConstant covariantNonnegative grade :=
  (finiteJetPair_oneHigh_payment parameters parameters.length grade loss lossLarge
    (covariantConstant grade) (productRecoveryCellConstant parameters positive product.coefficientBound 0)
    (covariantNonnegative grade)
    (productRecoveryCellConstant_nonnegative parameters positive product.coefficientBound 0)).choose_spec.1

/-- The reference transfer and finite lift preserve the independent low
source payment of the SAME recovered pair. -/
def actualProductFlatConstant (grade : ℕ) : ℝ :=
  ((originalRealFiniteLift_reference_bound_on_patch parameters parameters.length grade reference inside
      product.neighborhood.seedPatch product.neighborhood.compact product.neighborhood.patchInside).choose+
    (actualReferencePair_bound_on_patch parameters grade reference inside
      product.neighborhood.seedPatch product.neighborhood.compact product.neighborhood.patchInside).choose)*
  (1+actualProductPairConstant product loss lossLarge covariantConstant covariantNonnegative grade)

theorem actualProductFlatConstant_nonnegative (grade : ℕ) :
    0 ≤ actualProductFlatConstant product loss lossLarge covariantConstant covariantNonnegative grade :=
  mul_nonneg (add_nonneg
    (originalRealFiniteLift_reference_bound_on_patch parameters parameters.length grade reference inside
      product.neighborhood.seedPatch product.neighborhood.compact product.neighborhood.patchInside).choose_spec.1
    (actualReferencePair_bound_on_patch parameters grade reference inside
      product.neighborhood.seedPatch product.neighborhood.compact product.neighborhood.patchInside).choose_spec.1)
    (add_nonneg zero_le_one
      (actualProductPairConstant_nonnegative product loss lossLarge covariantConstant covariantNonnegative grade))

variable (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*parameters.length))
  (higher : ℕ) (higherLarge : 24 ≤ higher)
  (finite : OriginalFiniteParameter) (member : finite ∈ product.neighborhood.parameterDomain)
  (state : stateSmoothRange parameters reference inside)
  (low : stateSize parameters reference inside higher 0 state ≤ 2*product.neighborhood.radius)
  (source : OriginalFlatSource parameters parameters.length)

attribute [local irreducible] NativeRecoveryPacket.family NativeRecoveryPacket.covariant
  NativeRecoveryPacket.vector NativeRecoveryPacket.xi NativeRecoveryPacket.scalar actualFiniteCurrentField

variable (packet : ActualProductRecovery product widthHalf widthLength higher higherLarge finite member state low source)
  (covariantBound : ∀ grade, originalGradeNorm (parameters := parameters) grade packet.covariant ≤ covariantConstant grade*
    (‖quotientEta parameters (grade+loss) source.val.val‖+
      physicalBudget parameters (actualFiniteCurrentField parameters reference inside finite.1 (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state)) (finite.1 0) finite.2 (grade+loss)*‖quotientEta parameters loss source.val.val‖))

include packet covariantBound

/-- The actual U/S bound consumes only the full covariant norm. Its cell-zero
term and the literal residual/source payment were already proved in the packet. -/
theorem actualProductRecovery_pair_bound (grade : ℕ) :
    originalGradeNorm (parameters := parameters) grade packet.vector+originalGradeNorm (parameters := parameters) grade packet.scalar ≤
      actualProductPairConstant product loss lossLarge covariantConstant covariantNonnegative grade*
        (‖quotientEta parameters (grade+loss) source.val.val‖+
          physicalBudget parameters (actualFiniteCurrentField parameters reference inside finite.1 (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state)) (finite.1 0) finite.2 (grade+loss)*‖quotientEta parameters loss source.val.val‖) := by
  exact (finiteJetPair_oneHigh_payment parameters parameters.length grade loss lossLarge
    (covariantConstant grade) (productRecoveryCellConstant parameters positive product.coefficientBound 0)
    (covariantNonnegative grade)
    (productRecoveryCellConstant_nonnegative parameters positive product.coefficientBound 0)).choose_spec.2
      (finite.1 0) finite.2 (actualFiniteCurrentField parameters reference inside finite.1 (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state)) (actualJetExhaustion_cubicSmall parameters parameters.length product.coefficientBound
  reference inside finite.1 (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state) ((actualProduct_recovery_smallness product higher higherLarge finite member state low).1))
      (actualProduct_recovery_smallness product higher higherLarge finite member state low).2.1
      (actualFiniteCurrentScalar parameters reference inside finite.1 (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state))
      source.val.val packet.covariant packet.vector packet.scalar (packet.recovery grade)
      (covariantBound grade) (packet.cellBound 0)

/-- The reconstructed SAME original flat solution solves the literal
forward equation and carries its uniform reference one-high estimate. -/
theorem actualProductRecovery_flat_bound :
    ∃ reconstructed : stateSmoothRange parameters reference inside,
      literalPhysicalSmoothForward parameters parameters.length reference inside finite.1 (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state)
        ((product.neighborhood.raiseBase higher higherLarge).axis state low) reconstructed=source.val ∧
      ∀ grade, ‖Grad.SmoothingFamily.stateToGrade parameters grade reconstructed.val‖ ≤
        actualProductFlatConstant product loss lossLarge covariantConstant covariantNonnegative grade*
          (‖quotientEta parameters (grade+loss) source.val.val‖+
            physicalBudget parameters (actualFiniteCurrentField parameters reference inside finite.1 (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state)) (finite.1 0) finite.2 (grade+loss)*‖quotientEta parameters loss source.val.val‖) := by
  let constants := fun grade => productRecoveryNativeConstant parameters positive product.coefficientBound grade *
    (‖quotientEta parameters (grade+20) source.val.val‖+
      physicalBudget parameters (actualFiniteCurrentField parameters reference inside finite.1 (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state)) (finite.1 0) finite.2 (grade+20)*‖quotientEta parameters 20 source.val.val‖)
  have estimate (index grade) : ‖packet.family.graded index grade‖ ≤ constants grade := by
    apply le_trans _ (packet.nativeBound index grade)
    unfold NativeCartesianFamily.nativeNorm exhaustionDatumNorm originalWeightedDatumNorm
    exact le_add_of_nonneg_left (norm_nonneg _)
  exact actualNativeFlatSource_reference_oneHigh parameters product.coefficientBound positive widthHalf widthLength
    reference inside finite.1 (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state)
    ((product.neighborhood.raiseBase higher higherLarge).axis state low) ((actualProduct_recovery_smallness product higher higherLarge finite member state low).1) product.nonnegative
    (product.seedBound finite member 1) (product.seedBound finite member 2) (product.seedBound finite member 3)
    source product.neighborhood.seedPatch product.neighborhood.compact product.neighborhood.patchInside
    (product.neighborhood.seedInside finite member) packet.family constants estimate packet.vector packet.vectorSame
    packet.scalar packet.scalarSame loss lossLarge
    (actualProductPairConstant product loss lossLarge covariantConstant covariantNonnegative)
    (actualProductRecovery_pair_bound product loss lossLarge covariantConstant covariantNonnegative
      widthHalf widthLength higher higherLarge finite member state low source packet covariantBound)

end Grad.OriginalMainConsumer
