import AKDV27ActualProductAnnularNorm
import AKDV10CanonicalCompactCellPacket
import AKDW19SameAnnularCirclePlanarNorm

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

/-- The SAME canonical compact core inherits the actual annular high norm.
The circle operator acts at the same order and adds no source loss. -/
theorem actualProduct_compactAnnularNorm (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ finite (member : finite ∈ product.neighborhood.parameterDomain)
      (state : stateSmoothRange parameters reference inside)
      (low : stateSize parameters reference inside higher 0 state ≤ 2*product.neighborhood.radius)
      (source : OriginalFlatSource parameters parameters.length) (image : ACore parameters 3),
      (originalSourceMoments parameters image).field =
        startupCutoffL2 actualNativeAnnularCutoff actualNativeAnnularCutoff_smooth actualNativeAnnularCutoff_compact
          (originalSourceMoments parameters
            (canonicalProductCompactCore product widthHalf widthLength higher higherLarge finite member state low source)).field →
      originalPlanarNorm parameters grade image ≤ constant *
        (‖quotientEta parameters (grade+32) source.val.val‖+
          (1+physicalBudget parameters (actualFiniteCurrentField parameters reference inside finite.1
            (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state))
            (finite.1 0) finite.2 (grade+32))*‖quotientEta parameters 32 source.val.val‖) := by
  let circle := startupSameAnnularCircle_planarNorm grade
  let annular := actualProduct_covariantAnnularNorm product widthHalf widthLength higher higherLarge grade
  let circleConstant := circle.choose
  let annularConstant := annular.choose
  have circleNonnegative : 0 ≤ circleConstant := circle.choose_spec.1
  have annularNonnegative : 0 ≤ annularConstant := annular.choose_spec.1
  refine ⟨circleConstant*annularConstant,mul_nonneg circleNonnegative annularNonnegative,?_⟩
  intro finite member state low source image sameImage
  let packet := canonicalProductRecovery product widthHalf widthLength higher higherLarge finite member state low source
  let compactCore := canonicalProductCompactCore product widthHalf widthLength higher higherLarge finite member state low source
  let cutoff := startupOriginalCutoff_core_exists parameters actualNativeAnnularCutoff
    actualNativeAnnularCutoff_smooth actualNativeAnnularCutoff_compact packet.covariant
  let annularCovariant := cutoff.choose
  have sameCovariant := cutoff.choose_spec
  have covariantBound := annular.choose_spec.2 finite member state low source annularCovariant sameCovariant
  have circleBound := circle.choose_spec.2 parameters packet.covariant compactCore annularCovariant image
    (canonicalProductCompactCore_sameCircle product widthHalf widthLength higher higherLarge finite member state low source)
    sameCovariant sameImage
  exact circleBound.trans ((mul_le_mul_of_nonneg_left covariantBound circleNonnegative).trans_eq (mul_assoc _ _ _).symm)

/-- The compact annular base is paid independently by the fixed full source norm. -/
theorem actualProduct_compactAnnularBase :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ finite (member : finite ∈ product.neighborhood.parameterDomain)
      (state : stateSmoothRange parameters reference inside)
      (low : stateSize parameters reference inside higher 0 state ≤ 2*product.neighborhood.radius)
      (source : OriginalFlatSource parameters parameters.length) (image : ACore parameters 3),
      (originalSourceMoments parameters image).field =
        startupCutoffL2 actualNativeAnnularCutoff actualNativeAnnularCutoff_smooth actualNativeAnnularCutoff_compact
          (originalSourceMoments parameters
            (canonicalProductCompactCore product widthHalf widthLength higher higherLarge finite member state low source)).field →
      originalPlanarNorm parameters 0 image ≤ constant * ‖quotientEta parameters 32 source.val.val‖ := by
  let circle := startupSameAnnularCircle_planarNorm 0
  let annular := actualProduct_covariantAnnularBase product widthHalf widthLength higher higherLarge
  let circleConstant := circle.choose
  let annularConstant := annular.choose
  have circleNonnegative : 0 ≤ circleConstant := circle.choose_spec.1
  have annularNonnegative : 0 ≤ annularConstant := annular.choose_spec.1
  refine ⟨circleConstant*annularConstant,mul_nonneg circleNonnegative annularNonnegative,?_⟩
  intro finite member state low source image sameImage
  let packet := canonicalProductRecovery product widthHalf widthLength higher higherLarge finite member state low source
  let compactCore := canonicalProductCompactCore product widthHalf widthLength higher higherLarge finite member state low source
  let cutoff := startupOriginalCutoff_core_exists parameters actualNativeAnnularCutoff
    actualNativeAnnularCutoff_smooth actualNativeAnnularCutoff_compact packet.covariant
  let annularCovariant := cutoff.choose
  have sameCovariant := cutoff.choose_spec
  have covariantBound := annular.choose_spec.2 finite member state low source annularCovariant sameCovariant
  have circleBound := circle.choose_spec.2 parameters packet.covariant compactCore annularCovariant image
    (canonicalProductCompactCore_sameCircle product widthHalf widthLength higher higherLarge finite member state low source)
    sameCovariant sameImage
  exact circleBound.trans ((mul_le_mul_of_nonneg_left covariantBound circleNonnegative).trans_eq (mul_assoc _ _ _).symm)

end Grad.OriginalMainConsumer
