import AKT17CofinalNormTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 450000
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




/-- Actual higher-vanishing Cartesian data now produce a compatible full
original solution family on cofinal collars. No source norm, compatibility,
PDE, solution, or inserted-witness hypothesis is supplied by the caller. -/
theorem actualCartesianSource_compatibleSolution
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
          (graded : ∀ k (_t : ℕ), CoupledSpace (lower k) length (positive k) lengthPositive),
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
                ‖quotientEta parameters 8 source‖)) := by
  let allGrades := actualCartesianSource_cofinalWitnesses parameters length compact lengthPositive M Mnonnegative
  refine ⟨allGrades.choose, allGrades.choose_spec.1, ?_⟩
  intro widthHalf widthLength state small stateBound source flat vanishing
  dsimp only
  let lower := originalExhaustionRadius length
  let positive := originalExhaustionRadius_positive length lengthPositive
  let half := originalExhaustionRadius_half length lengthPositive
  let data := fun index => cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0
  let sourceBound := originalSourceAllocationConstant parameters length 0 * (1 + M) * ‖quotientEta parameters 8 source‖
  have sourceNonnegative : 0 ≤ sourceBound :=
    mul_nonneg (mul_nonneg (originalSourceAllocationConstant_positive parameters length 0).le (by positivity)) (norm_nonneg _)
  let witnesses := allGrades.choose_spec.2 widthHalf widthLength state small stateBound source flat vanishing
  let retained : ∀ (_t : ℕ) n, CoupledSpace (lower n) length (positive n) lengthPositive := witnesses.choose
  let gradeBound := fun t => allGrades.choose t * (‖quotientEta parameters (t + 8) source‖ +
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (t + 14) * ‖quotientEta parameters 8 source‖)
  have actual := fun t n => cartesianExhaustionInserted_observation parameters length compact lengthPositive widthHalf widthLength state small
    source flat t n (retained t n) (witnesses.choose_spec t n).1
  have uniform (t n : ℕ) : ‖retained t n‖ ≤ gradeBound t := by
    have bound := (witnesses.choose_spec t n).2
    have same := cartesianExhaustionContext_norm parameters length compact lengthPositive widthHalf widthLength state small n (witnesses.choose t n)
    have budgetSame : allGrades.choose t * (‖quotientEta parameters (t + 8) source‖ +
        physicalBudget parameters
          (cartesianExhaustionContext parameters length compact lengthPositive widthHalf widthLength state small n).state.val.val.field
          (cartesianExhaustionContext parameters length compact lengthPositive widthHalf widthLength state small n).state.val.val.rho
          (cartesianExhaustionContext parameters length compact lengthPositive widthHalf widthLength state small n).state.val.val.epsilon
          (t + 14) * ‖quotientEta parameters 8 source‖) = gradeBound t := rfl
    linarith only [bound,same,budgetSame]
  have sourceCompatible := fun first second included => cartesianExhaustionDatum_restrict parameters length compact lengthPositive widthHalf widthLength state small
    source flat first second 0 included
  have sourceEstimate := fun index => cartesianExhaustionDatum_base_bound parameters length compact lengthPositive widthHalf widthLength state small
    M stateBound source flat vanishing index
  let solved := actualOriginalSolves_have_compatibleAllGradeLimit parameters length compact lengthPositive widthHalf widthLength state
    (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    lower positive half (originalExhaustionRadius_cofinal length lengthPositive) data
    sourceCompatible sourceBound sourceNonnegative sourceEstimate retained actual gradeBound uniform
  refine Exists.elim solved ?_
  intro limit remainder
  refine Exists.elim remainder ?_
  intro graded remainder
  refine Exists.elim remainder ?_
  intro subsequence laws
  refine ⟨limit,graded,?_⟩
  constructor
  · intro k
    exact laws.2.2.1 k
  · constructor
    · exact laws.2.2.2.1
    · intro k t
      constructor
      · exact (laws.2.2.2.2 k t).1
      · have finalBound := (laws.2.2.2.2 k t).2
        have exactBudget : gradeBound t = allGrades.choose t * (‖quotientEta parameters (t + 8) source‖ +
            physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (t + 14) *
              ‖quotientEta parameters 8 source‖) := rfl
        linarith only [finalBound,exactBudget]


end Grad.ActualPuncturedFamily
