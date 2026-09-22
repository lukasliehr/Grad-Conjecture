import AKDV3SameProductFlatOneHigh
import AKDS26ActualProductInverseBound
import AKDU6ExactMainTypedInverseConsumer

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



attribute [local irreducible] canonicalProductRecovery NativeRecoveryPacket.family
  NativeRecoveryPacket.covariant NativeRecoveryPacket.vector NativeRecoveryPacket.scalar actualFiniteCurrentField

variable {parameters : PhaseParameters} {positive : 0 < parameters.length}
  {reference : Seed.Parameters} {inside : reference ∈ Seed.parameterDomain} {center : Seed.Parameters}

/-- The remaining analytic input concerns only the full covariant norm of
the canonical SAME recovery. All native/cell/source/field premises are proved. -/
structure ActualProductCovariantOneHigh
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
      (canonicalProductRecovery product widthHalf widthLength higher higherLarge finite member state low source).covariant ≤
      constant grade*(‖quotientEta parameters (grade+loss) source.val.val‖+
        physicalBudget parameters (actualFiniteCurrentField parameters reference inside finite.1
          (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state))
          (finite.1 0) finite.2 (grade+loss)*‖quotientEta parameters loss source.val.val‖)

namespace ActualProductCovariantOneHigh
variable {product : OriginalPhysicalProduct parameters positive reference inside center}
  {widthHalf : parameters.gamma ≤ 1/2} {widthLength : parameters.gamma ≤ Real.sqrt 5/(6*parameters.length)}
  {higher : ℕ} {higherLarge : 24 ≤ higher} {loss : ℕ}
  (estimate : ActualProductCovariantOneHigh product widthHalf widthLength higher higherLarge loss)
  (lossLarge : 20 ≤ loss)

include estimate lossLarge in
/-- Exact DS26 flatSolve, with every constant fixed before state and source. -/
theorem actual_flatSolve :
    ∃ constants : ℕ → ℝ, (∀ grade, 0 ≤ constants grade) ∧
      ∀ finite (member : finite ∈ product.neighborhood.parameterDomain)
      (state : stateSmoothRange parameters reference inside)
      (low : stateSize parameters reference inside higher 0 state ≤ 2*product.neighborhood.radius)
      (source : OriginalFlatSource parameters parameters.length),
      ∃ reconstructed : stateSmoothRange parameters reference inside,
        literalPhysicalSmoothForward parameters parameters.length reference inside finite.1
          (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state)
          ((product.neighborhood.raiseBase higher higherLarge).axis state low) reconstructed=source.val ∧
        ∀ grade, ‖Grad.SmoothingFamily.stateToGrade parameters grade reconstructed.val‖ ≤ constants grade*
          (‖quotientEta parameters (grade+loss) source.val.val‖+
            physicalBudget parameters (actualFiniteCurrentField parameters reference inside finite.1
              (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state))
              (finite.1 0) finite.2 (grade+loss)*‖quotientEta parameters loss source.val.val‖) := by
  refine ⟨actualProductFlatConstant product loss lossLarge estimate.constant estimate.nonnegative,
    actualProductFlatConstant_nonnegative product loss lossLarge estimate.constant estimate.nonnegative, ?_⟩
  intro finite member state low source
  exact actualProductRecovery_flat_bound product loss lossLarge estimate.constant estimate.nonnegative
    widthHalf widthLength higher higherLarge finite member state low source
    (canonicalProductRecovery product widthHalf widthLength higher higherLarge finite member state low source)
    (estimate.bounded finite member state low source)

include estimate lossLarge in
/-- The recovered flat estimate feeds the actual full-source inverse map;
its only loss increase is the already checked nine-grade projection payment. -/
theorem actual_original_oneHigh (lowFits : loss+6 ≤ higher) :
    Nonempty (ActualProductOneHigh product widthHalf widthLength higher (loss+9)) := by
  let flat := estimate.actual_flatSolve lossLarge
  let flatConstants := flat.choose
  have flatNonnegative := flat.choose_spec.1
  have flatSolve := flat.choose_spec.2
  let bound := product.inverseMap_bound_of_actual_flat widthHalf widthLength higher loss higherLarge lossLarge lowFits
    flatConstants flatNonnegative flatSolve
  exact ⟨{
    baseLarge := higherLarge
    constant := bound.choose
    nonnegative := bound.choose_spec.1
    bounded := bound.choose_spec.2 }⟩

include lossLarge in
/-- The exact original family follows with the same parameter product,
chosen Newton scale, actual two-sided inverse and all geometric conclusions. -/
theorem actual_cell_family
    {product : OriginalPhysicalProduct parameters positive reference inside originalSeedCenter}
    (estimate : ActualProductCovariantOneHigh product widthHalf widthLength higher higherLarge loss)
    (lowFits : loss+6 ≤ higher) : Nonempty (Grad.PhysicalFamily.CellSolutionFamily parameters.length) := by
  let inverse := Classical.choice (estimate.actual_original_oneHigh lossLarge lowFits)
  exact actual_cell_family_of_product_oneHigh inverse (by omega)

end ActualProductCovariantOneHigh
end Grad.OriginalMainConsumer
