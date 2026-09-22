import AKX1SameOriginalGraphCovariants

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.ActualPuncturedReconstruction
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





open Grad.AnnularPhysicalReconstruction Grad.AnnularKernelL2 Grad.SourceCollarDivision


/-- Radius-uniform physical reconstruction on arbitrary original full graph
points. Its bound uses the native retained norm and the actual BF datum norm. -/
theorem originalGraphCovariants_uniform (parameters : PhaseParameters) (length compact : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)
        (state : RetainedInverseState parameters length compact)
        (data : OriginalStrongCarrier parameters lower 0 0)
        (point : OriginalFiveBlockAmbient parameters lower length positive),
        ‖originalGraphCovariant parameters length compact lower positive bounded lengthPositive state data point‖ +
          ‖originalGraphRotatedCovariant parameters length compact lower positive bounded lengthPositive state data point‖ ≤
          constant * (1 + physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 7) *
            ((11 + 4 * length) * originalWeightedRetainedNorm parameters lower length positive bounded lengthPositive point.ofLp.1 +
              3 * originalWeightedDatumNorm parameters lower length positive bounded lengthPositive data) := by
  obtain ⟨constant,nonnegative,estimate⟩ := sharedFullReconstruction_uniform parameters length compact
  refine ⟨constant,nonnegative,?_⟩
  intro lower positive bounded lengthPositive state data point
  rw [originalGraphCovariant_shared,originalGraphRotatedCovariant_shared]
  have actual := estimate lower positive bounded lengthPositive state.val
    (originalWeightedDatum parameters lower length positive bounded lengthPositive data)
    (originalWeightedRetainedObservation parameters lower length positive bounded lengthPositive point)
  have retainedNorm : ‖originalWeightedRetainedObservation parameters lower length positive bounded lengthPositive point‖ =
      originalWeightedRetainedNorm parameters lower length positive bounded lengthPositive point.ofLp.1 := rfl
  have datumNorm : ‖originalWeightedDatum parameters lower length positive bounded lengthPositive data‖ =
      originalWeightedDatumNorm parameters lower length positive bounded lengthPositive data := rfl
  have payment := congrArg₂ (fun retained datum : ℝ =>
    constant * (1 + physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 7) *
      ((11 + 4 * length) * retained + 3 * datum)) retainedNorm datumNorm
  linarith only [actual,payment]


/-- Zero independent boundary data retain every actual source coordinate;
only their already controlled EX source norm enters this reconstruction. -/
theorem originalGraphCovariants_exhaustion_bound (parameters : PhaseParameters) (length compact : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (context : CoupledCoordinateContext parameters length compact)
        (data : OriginalStrongCarrier parameters context.lower 0 0)
        (point : OriginalFiveBlockAmbient parameters context.lower length context.positive),
        ‖originalGraphCovariant parameters length compact context.lower context.positive
            (context.lowerHalf.trans (by norm_num)) context.lengthPositive context.state
            (zeroBoundaryDatum parameters context.lower data) point‖ +
          ‖originalGraphRotatedCovariant parameters length compact context.lower context.positive
            (context.lowerHalf.trans (by norm_num)) context.lengthPositive context.state
            (zeroBoundaryDatum parameters context.lower data) point‖ ≤
          constant * (1 + physicalBudget parameters context.state.val.val.field context.state.val.val.rho context.state.val.val.epsilon 7) *
            ((11 + 4 * length) * originalWeightedRetainedNorm parameters context.lower length context.positive
              (context.lowerHalf.trans (by norm_num)) context.lengthPositive point.ofLp.1 +
              3 * exhaustionDatumNorm parameters length compact context data) := by
  obtain ⟨constant,nonnegative,estimate⟩ := originalGraphCovariants_uniform parameters length compact
  refine ⟨constant,nonnegative,?_⟩
  intro context data point
  exact estimate context.lower context.positive (context.lowerHalf.trans (by norm_num)) context.lengthPositive
    context.state (zeroBoundaryDatum parameters context.lower data) point

end Grad.ActualPuncturedReconstruction
