import AKDV29FixedBase32PlanarAbsorption
import AKDV10CanonicalCompactCellPacket
import AKDS40FiniteJetHighRankAbsorption

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




open Grad.GaugeCoefficients.Physical.RadialLedger
attribute [local irreducible] canonicalProductRecovery NativeRecoveryPacket.family
  NativeRecoveryPacket.covariant NativeRecoveryPacket.vector NativeRecoveryPacket.scalar actualFiniteCurrentField

variable {parameters : PhaseParameters} {positive : 0 < parameters.length}
  {reference : Seed.Parameters} {inside : reference ∈ Seed.parameterDomain} {center : Seed.Parameters}

/-- The full norm of the SAME canonical compact core. -/
structure ActualProductCompactOneHigh
    (product : OriginalPhysicalProduct parameters positive reference inside center)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*parameters.length))
    (higher : ℕ) (higherLarge : 24 ≤ higher) (loss : ℕ) where
  constant : ℕ → ℝ
  nonnegative : ∀ grade, 0 ≤ constant grade
  bounded : ∀ finite (member : finite ∈ product.neighborhood.parameterDomain)
    (state : stateSmoothRange parameters reference inside)
    (low : stateSize parameters reference inside higher 0 state ≤ 2*product.neighborhood.radius)
    (source : OriginalFlatSource parameters parameters.length) (grade : ℕ),
    originalGradeNorm (parameters := parameters) grade
      (canonicalProductCompactCore product widthHalf widthLength higher higherLarge finite member state low source) ≤
      constant grade*(‖quotientEta parameters (grade+loss) source.val.val‖+
        physicalBudget parameters (actualFiniteCurrentField parameters reference inside finite.1
          (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state))
          (finite.1 0) finite.2 (grade+loss)*‖quotientEta parameters loss source.val.val‖)

/-- The actual compact planar estimate is only required from rank two. -/
structure ActualProductCompactPlanarEstimate
    (product : OriginalPhysicalProduct parameters positive reference inside center)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*parameters.length))
    (higher : ℕ) (higherLarge : 24 ≤ higher) (shift : ℕ) where
  constant : ℕ → ℝ
  nonnegative : ∀ grade, 0 ≤ constant grade
  bounded : ∀ finite (member : finite ∈ product.neighborhood.parameterDomain)
    (state : stateSmoothRange parameters reference inside)
    (low : stateSize parameters reference inside higher 0 state ≤ 2*product.neighborhood.radius)
    (source : OriginalFlatSource parameters parameters.length) (grade : ℕ), 2 ≤ grade →
    let core := canonicalProductCompactCore product widthHalf widthLength higher higherLarge finite member state low source
    let field := actualFiniteCurrentField parameters reference inside finite.1
      (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state)
    originalPlanarNorm parameters grade core ≤
      (1/(4*apMassEndpointConstant 0 grade+2))*originalGradeNorm (parameters := parameters) grade core+
      constant grade*(originalCellNorm parameters (grade+shift) core+
        (1+physicalBudget parameters field (finite.1 0) finite.2 (grade+shift+32))*originalGradeNorm 0 core+
        ‖quotientEta parameters (grade+shift+32) source.val.val‖+
        (1+physicalBudget parameters field (finite.1 0) finite.2 (grade+shift+32))*‖quotientEta parameters 32 source.val.val‖)

namespace ActualProductCompactPlanarEstimate
variable {product : OriginalPhysicalProduct parameters positive reference inside center}
  {widthHalf : parameters.gamma ≤ 1/2} {widthLength : parameters.gamma ≤ Real.sqrt 5/(6*parameters.length)}
  {higher : ℕ} {higherLarge : 24 ≤ higher} {shift : ℕ}
  (estimate : ActualProductCompactPlanarEstimate product widthHalf widthLength higher higherLarge shift)
  (loss : ℕ) (lossLarge : shift+32 ≤ loss)

/-- Absorb the compact core first. Ranks zero and one use the checked
rank-two bound, costing one fixed additional loss of two. -/
def toCompactOneHigh : ActualProductCompactOneHigh product widthHalf widthLength higher higherLarge (loss+2) where
  constant := (finiteJetCore_oneHigh_of_planar_ge_two_base32 parameters shift loss lossLarge
    (productCompactCellConstant parameters positive product.coefficientBound) estimate.constant
    (productCompactCellConstant_nonnegative parameters positive product.coefficientBound) estimate.nonnegative).choose
  nonnegative := (finiteJetCore_oneHigh_of_planar_ge_two_base32 parameters shift loss lossLarge
    (productCompactCellConstant parameters positive product.coefficientBound) estimate.constant
    (productCompactCellConstant_nonnegative parameters positive product.coefficientBound) estimate.nonnegative).choose_spec.1
  bounded := by
    intro finite member state low source grade
    exact (finiteJetCore_oneHigh_of_planar_ge_two_base32 parameters shift loss lossLarge
      (productCompactCellConstant parameters positive product.coefficientBound) estimate.constant
      (productCompactCellConstant_nonnegative parameters positive product.coefficientBound) estimate.nonnegative).choose_spec.2
      (finite.1 0) finite.2
      (actualFiniteCurrentField parameters reference inside finite.1
        (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state))
      source.val.val (canonicalProductCompactCore product widthHalf widthLength higher higherLarge finite member state low source)
      (actualProduct_recovery_smallness product higher higherLarge finite member state low).2.1
      (canonicalProductCompactCore_cellBound product widthHalf widthLength higher higherLarge finite member state low source)
      (estimate.bounded finite member state low source) grade

end ActualProductCompactPlanarEstimate
end Grad.OriginalMainConsumer
