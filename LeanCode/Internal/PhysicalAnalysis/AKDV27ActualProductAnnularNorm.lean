import AKDV2CanonicalSameProductRecovery
import AKEC2ActualFiniteNativeAnnularBase

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

open Grad.OriginalCollarNorm Grad.ActualOriginalSourceMoments
variable {parameters : PhaseParameters} {positive : 0 < parameters.length}
  {reference : Seed.Parameters} {inside : reference ∈ Seed.parameterDomain} {center : Seed.Parameters}
  (product : OriginalPhysicalProduct parameters positive reference inside center)
  (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*parameters.length))
  (higher : ℕ) (higherLarge : 24 ≤ higher)

/-- Actual canonical-product annular bound, with one fixed full-source base32.
The native residual estimate and all core/field identities come from the SAME packet. -/
theorem actualProduct_covariantAnnularNorm (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ finite (member : finite ∈ product.neighborhood.parameterDomain)
      (state : stateSmoothRange parameters reference inside)
      (low : stateSize parameters reference inside higher 0 state ≤ 2*product.neighborhood.radius)
      (source : OriginalFlatSource parameters parameters.length) (image : ACore parameters 3),
      (originalSourceMoments parameters image).field =
        startupCutoffL2 actualNativeAnnularCutoff actualNativeAnnularCutoff_smooth actualNativeAnnularCutoff_compact
          (originalSourceMoments parameters
            (canonicalProductRecovery product widthHalf widthLength higher higherLarge finite member state low source).covariant).field →
      originalPlanarNorm parameters grade image ≤ constant *
        (‖quotientEta parameters (grade+32) source.val.val‖+
          (1+physicalBudget parameters (actualFiniteCurrentField parameters reference inside finite.1
            (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state))
            (finite.1 0) finite.2 (grade+32))*‖quotientEta parameters 32 source.val.val‖) := by
  let certificate := actualFiniteCovariant_annularPlanarNorm parameters parameters.length product.coefficientBound positive
    widthHalf widthLength grade (productRecoveryResidualNativeConstant parameters positive product.coefficientBound)
    (productRecoveryResidualNativeConstant_nonnegative parameters positive product.coefficientBound)
  let constant := certificate.choose
  have nonnegative : 0 ≤ constant := certificate.choose_spec.1
  have bound := certificate.choose_spec.2
  refine ⟨constant,nonnegative,?_⟩
  intro finite member state low source image sameImage
  let insideS := product.neighborhood.patchInside (product.neighborhood.seedInside finite member)
  let field := actualFiniteCurrentField parameters reference inside finite.1 insideS (finite.2,state)
  let packet := canonicalProductRecovery product widthHalf widthLength higher higherLarge finite member state low source
  have stateSmall := product.neighborhood.raiseBase_low higher higherLarge state low
  have bounded : physicalBudget parameters field (finite.1 0) finite.2 24 ≤ 1 :=
    (product.budget finite member state stateSmall).le.trans (min_le_left _ _)
  have small := (actualProduct_recovery_smallness product higher higherLarge finite member state low).1
  have estimate := bound reference inside finite.1 insideS (finite.2,state)
    ((product.neighborhood.raiseBase higher higherLarge).axis state low) product.nonnegative
    (product.seedBound finite member 1) (product.seedBound finite member 2) (product.seedBound finite member 3)
    small bounded source packet.family (packet.residualNativeBound 3) packet.covariant packet.covariantSame image sameImage
  exact estimate.trans (mul_le_mul_of_nonneg_left (add_le_add
    (referenceSource_norm_mono parameters (by omega : grade+24≤grade+32) source.val.val)
    (mul_le_mul (add_le_add (le_refl _) (physicalBudget_monotone parameters field (finite.1 0) finite.2 (by omega : grade+24≤grade+32)))
      (referenceSource_norm_mono parameters (by norm_num : 24≤32) source.val.val) (norm_nonneg _)
      (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)))) nonnegative)

/-- The actual annular base is independent of every high state norm.
It uses B24 from the product before promoting the fixed source base to32. -/
theorem actualProduct_covariantAnnularBase :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ finite (member : finite ∈ product.neighborhood.parameterDomain)
      (state : stateSmoothRange parameters reference inside)
      (low : stateSize parameters reference inside higher 0 state ≤ 2*product.neighborhood.radius)
      (source : OriginalFlatSource parameters parameters.length) (image : ACore parameters 3),
      (originalSourceMoments parameters image).field =
        startupCutoffL2 actualNativeAnnularCutoff actualNativeAnnularCutoff_smooth actualNativeAnnularCutoff_compact
          (originalSourceMoments parameters
            (canonicalProductRecovery product widthHalf widthLength higher higherLarge finite member state low source).covariant).field →
      originalPlanarNorm parameters 0 image ≤ constant * ‖quotientEta parameters 32 source.val.val‖ := by
  let certificate := actualFiniteCovariant_annularBaseNorm parameters parameters.length product.coefficientBound positive
    widthHalf widthLength (productRecoveryResidualNativeConstant parameters positive product.coefficientBound)
    (productRecoveryResidualNativeConstant_nonnegative parameters positive product.coefficientBound)
  let constant := certificate.choose
  have nonnegative : 0 ≤ constant := certificate.choose_spec.1
  have bound := certificate.choose_spec.2
  refine ⟨constant,nonnegative,?_⟩
  intro finite member state low source image sameImage
  let insideS := product.neighborhood.patchInside (product.neighborhood.seedInside finite member)
  let field := actualFiniteCurrentField parameters reference inside finite.1 insideS (finite.2,state)
  let packet := canonicalProductRecovery product widthHalf widthLength higher higherLarge finite member state low source
  have stateSmall := product.neighborhood.raiseBase_low higher higherLarge state low
  have bounded : physicalBudget parameters field (finite.1 0) finite.2 24 ≤ 1 :=
    (product.budget finite member state stateSmall).le.trans (min_le_left _ _)
  have small := (actualProduct_recovery_smallness product higher higherLarge finite member state low).1
  have estimate := bound reference inside finite.1 insideS (finite.2,state)
    ((product.neighborhood.raiseBase higher higherLarge).axis state low) product.nonnegative
    (product.seedBound finite member 1) (product.seedBound finite member 2) (product.seedBound finite member 3)
    small bounded source packet.family (packet.residualNativeBound 3) packet.covariant packet.covariantSame image sameImage
  exact estimate.trans (mul_le_mul_of_nonneg_left
    (referenceSource_norm_mono parameters (by norm_num : 24≤32) source.val.val) nonnegative)

end Grad.OriginalMainConsumer
