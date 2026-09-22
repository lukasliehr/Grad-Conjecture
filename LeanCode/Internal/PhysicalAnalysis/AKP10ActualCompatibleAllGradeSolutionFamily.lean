import AKP8SameCofinalAllGradeLimits
import AKP9OriginalAdmissibleCofinalRadii

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open Set Filter
open scoped Topology
namespace Grad.ActualAnnularExhaustion
open Grad.CartesianState Grad.AnnularFullGraph Grad.AnnularForwardDatum Grad.AnnularStrongOrbit
open Grad.AnnularForwardTraces Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularRestriction
open Grad.AnnularExhaustionEstimate Grad.AnnularWeakExhaustion Grad.AnnularFullSource
open Grad.AnnularHighGenerators
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

/-- The SAME actual annular solutions have a compatible full original limit
with every inserted grade and unchanged radius-independent bounds. -/
theorem actualOriginalSolves_have_compatibleAllGradeLimit
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact)
    (lower : ℕ → ℝ) (positive : ∀ n, 0 < lower n) (lowerHalf : ∀ n, lower n ≤ 1 / 2)
    (cofinal : ∀ k, ∀ᶠ n in atTop, lower n ≤ lower k)
    (data : ∀ n, OriginalStrongCarrier parameters (lower n) 0 0)
    (sourceCompatible : ∀ n k (included : lower n ≤ lower k),
      originalFullSourceRestriction parameters (lower n) (lower k) included (data n).val.ofLp.1 = (data k).val.ofLp.1)
    (sourceBound : ℝ) (sourceNonnegative : 0 ≤ sourceBound)
    (sourceEstimate : ∀ n, originalWeightedDatumNorm parameters (lower n) length (positive n)
      ((lowerHalf n).trans (by norm_num)) lengthPositive (zeroBoundaryDatum parameters (lower n) (data n)) ≤ sourceBound) :
    let solves := fun n => fixedExhaustionSolve parameters length compact lengthPositive widthHalf widthLength state small
      (lower n) (positive n) (lowerHalf n) (data n)
    ∀ (retained : ∀ (_t : ℕ) n, CoupledSpace (lower n) length (positive n) lengthPositive)
      (_actual : ∀ t n, CoupledInsertedGrade (lower n) length (positive n) lengthPositive t
        (originalWeightedRetainedObservation parameters (lower n) length (positive n) ((lowerHalf n).trans (by norm_num)) lengthPositive (solves n)) (retained t n))
      (gradeBound : ℕ → ℝ) (_uniform : ∀ t n, ‖retained t n‖ ≤ gradeBound t),
    ∃ (limit : ∀ k, OriginalFiveBlockAmbient parameters (lower k) length (positive k))
      (graded : ∀ k (_t : ℕ), CoupledSpace (lower k) length (positive k) lengthPositive)
      (subsequence : ℕ → ℕ), StrictMono subsequence ∧
      (∀ k, WeakConverges
        (cofinalRestrictionSequence parameters length lengthPositive lower positive lowerHalf solves k ∘ subsequence) (limit k)) ∧
      (∀ k, limit k ∈ OriginalObservedEquationGraph parameters length compact (lower k) (positive k)
        (lowerHalf k) lengthPositive widthHalf widthLength state ∧
        (limit k).ofLp.2 = (data k).val.ofLp.1 ∧
        originalOuterBoundaryTrace parameters length compact (lower k) (positive k) (lowerHalf k) lengthPositive state
          ((limit k).ofLp.1,(limit k).ofLp.2.ofLp.1) = 0 ∧
        originalWeightedRetainedNorm parameters (lower k) length (positive k) ((lowerHalf k).trans (by norm_num)) lengthPositive
          (limit k).ofLp.1 ≤ 2 * independentCoupledDataConstant parameters length compact * sourceBound) ∧
      (∀ k l (included : lower k ≤ lower l),
        originalFiveBlockRestriction parameters (lower k) (lower l) length (positive k) (positive l)
          ((lowerHalf l).trans_lt (by norm_num)) lengthPositive included (limit k) = limit l) ∧
      (∀ k t, CoupledInsertedGrade (lower k) length (positive k) lengthPositive t
        (originalWeightedRetainedObservation parameters (lower k) length (positive k) ((lowerHalf k).trans (by norm_num)) lengthPositive (limit k))
        (graded k t) ∧ ‖graded k t‖ ≤ gradeBound t) := by
  dsimp only
  intro retained actual gradeBound uniform
  let base := actualOriginalSolves_have_compatibleWeakLimit parameters length compact lengthPositive widthHalf widthLength state small
    lower positive lowerHalf cofinal data sourceCompatible sourceBound sourceNonnegative sourceEstimate
  let limit := base.choose
  let subsequence := base.choose_spec.choose
  have laws := base.choose_spec.choose_spec
  let allGrades := actualCofinal_allGradeLimits parameters length lengthPositive
    lower positive lowerHalf cofinal _ limit subsequence laws.1 laws.2.1 retained actual gradeBound uniform
  let graded := allGrades.choose
  let further := allGrades.choose_spec.choose
  have gradeLaws := allGrades.choose_spec.choose_spec
  exact ⟨limit,graded,subsequence ∘ further,laws.1.comp gradeLaws.1,gradeLaws.2.1,laws.2.2.1,laws.2.2.2,gradeLaws.2.2⟩

end Grad.ActualAnnularExhaustion
