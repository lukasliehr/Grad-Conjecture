import AKT13ActualCartesianCompatibleSolution
import AKT14ActualFullFamilyPhysicalRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.ActualPuncturedFamily
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




/-- Actual Cartesian data construct one punctured physical pair with the same
original full equation, all inserted bounds and exact closed-collar coefficients. -/
theorem actualCartesianSource_puncturedPhysicalFamily
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (M : ℝ) (Mnonnegative : 0 ≤ M) :
    ∃ constant : ℕ → ℝ, (∀ grade, 0 ≤ constant grade) ∧
      ∀ (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
        (state : RetainedInverseState parameters length compact)
        (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
          originalExhaustionPrimitiveRadius parameters length compact)
        (_stateBound : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14 ≤ M)
        (source : SmoothQuotient parameters) (flat : IsFlat source) (_vanishing : SourceHigherVanishing source),
        let lower := originalExhaustionRadius length
        let positive := originalExhaustionRadius_positive length lengthPositive
        let half := originalExhaustionRadius_half length lengthPositive
        let data := cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat
        ∃ (limit : ∀ k, OriginalFiveBlockAmbient parameters (lower k) length (positive k))
          (graded : ∀ k (_t : ℕ), CoupledSpace (lower k) length (positive k) lengthPositive)
          (physical : ℕ → ℝ → Grad.SourceCollarCoefficients.CellL2 1 × Grad.SourceCollarCoefficients.CellL2 1),
          (∀ k, limit k ∈ OriginalObservedEquationGraph parameters length compact (lower k) (positive k)
            (half k) lengthPositive widthHalf widthLength state ∧
            (limit k).ofLp.2 = (data k 0).val.ofLp.1 ∧
            originalOuterBoundaryTrace parameters length compact (lower k) (positive k) (half k) lengthPositive state
              ((limit k).ofLp.1,(limit k).ofLp.2.ofLp.1) = 0 ∧
            originalWeightedRetainedNorm parameters (lower k) length (positive k) ((half k).trans (by norm_num)) lengthPositive
              (limit k).ofLp.1 ≤ 2 * independentCoupledDataConstant parameters length compact *
                (originalSourceAllocationConstant parameters length 0 * (1 + M) * ‖quotientEta parameters 8 source‖)) ∧
          (∀ k l (included : lower k ≤ lower l),
            originalFiveBlockRestriction parameters (lower k) (lower l) length (positive k) (positive l)
              ((half l).trans_lt (by norm_num)) lengthPositive included (limit k) = limit l) ∧
          (∀ k t, CoupledInsertedGrade (lower k) length (positive k) lengthPositive t
            (originalWeightedRetainedObservation parameters (lower k) length (positive k) ((half k).trans (by norm_num)) lengthPositive (limit k))
            (graded k t) ∧ ‖graded k t‖ ≤ constant t * (‖quotientEta parameters (t + 8) source‖ +
              physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (t + 14) *
                ‖quotientEta parameters 8 source‖)) ∧
          (∀ t, ContinuousOn (physical t) (Ioc (0 : ℝ) 1)) ∧
          (∀ t k (radius : ℝ) (inside : radius ∈ Icc (lower k) 1) (mode : ℤ × ℤ),
            ((physical t radius).1 mode,(physical t radius).2 mode) =
              (Grad.AnnularSmoothCore.sameCoupledXCoefficient parameters (lower k) length (positive k)
                ((half k).trans_lt (by norm_num)) lengthPositive
                (originalWeightedRetainedObservation parameters (lower k) length (positive k)
                  ((half k).trans (by norm_num)) lengthPositive (limit k)) t ⟨radius,inside⟩ mode,
               Grad.AnnularSmoothCore.sameCoupledXiCoefficient parameters (lower k) length (positive k)
                ((half k).trans_lt (by norm_num)) lengthPositive
                (originalWeightedRetainedObservation parameters (lower k) length (positive k)
                  ((half k).trans (by norm_num)) lengthPositive (limit k)) t ⟨radius,inside⟩ mode)) := by
  let certificate := actualCartesianSource_compatibleSolution parameters length compact lengthPositive M Mnonnegative
  refine ⟨certificate.choose,certificate.choose_spec.1,?_⟩
  intro widthHalf widthLength state small stateBound source flat vanishing
  dsimp only
  have existsFamily := certificate.choose_spec.2 widthHalf widthLength state small stateBound source flat vanishing
  refine Exists.elim existsFamily ?_
  intro limit remainder
  refine Exists.elim remainder ?_
  intro graded laws
  let lower := originalExhaustionRadius length
  let positive := originalExhaustionRadius_positive length lengthPositive
  let bounded : ∀ index, lower index < 1 := fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)
  let cofinal := originalExhaustionRadius_tendsto length
  let inserted := fun index t => (laws.2.2 index t).1
  let physical : ℕ → ℝ → Grad.SourceCollarCoefficients.CellL2 1 × Grad.SourceCollarCoefficients.CellL2 1 := fun t => originalFamilyPhysicalPair parameters length lengthPositive lower positive bounded cofinal limit graded inserted t
  refine ⟨limit,graded,physical,laws.1,laws.2.1,laws.2.2,?_,?_⟩
  · intro t
    exact originalFamilyPhysicalPair_continuous parameters length lengthPositive lower positive bounded
      (originalExhaustionRadius_antitone length lengthPositive) cofinal limit graded inserted laws.2.1 t
  · intro t k radius inside mode
    have same := originalFamilyPhysicalPair_same parameters length lengthPositive lower positive bounded
      (originalExhaustionRadius_antitone length lengthPositive) cofinal limit graded inserted laws.2.1 t k radius inside mode
    exact same

end Grad.ActualPuncturedFamily
