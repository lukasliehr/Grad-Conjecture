import AKP4CofinalSequenceOriginalEquationsAndBounds

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
open Grad.GaugeCoefficients.Physical.Allocation
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule
  sourceRadialRealInner sourceGraphRealInner sourceKnownGraphRealInner
  weakRetainedRealInner weakSourcesRealInner weakFiveRealInner

/-- The actual accepted annular inverses produce compatible full original
weak solutions down to the axis. The inputs concern only the SAME prescribed
source family and its uniform weighted norm, never a solution or PDE assumption. -/
theorem actualOriginalSolves_have_compatibleWeakLimit
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
    ∃ (limit : ∀ k, OriginalFiveBlockAmbient parameters (lower k) length (positive k))
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
          ((lowerHalf l).trans_lt (by norm_num)) lengthPositive included (limit k) = limit l) := by
  dsimp only
  let solves := fun n => fixedExhaustionSolve parameters length compact lengthPositive widthHalf widthLength state small
    (lower n) (positive n) (lowerHalf n) (data n)
  let sources := fun n => (data n).val.ofLp.1
  let constant := 2 * independentCoupledDataConstant parameters length compact * sourceBound
  have coefficientNonnegative : 0 ≤ 2 * independentCoupledDataConstant parameters length compact :=
    mul_nonneg (by norm_num) (independentCoupledDataConstant_nonnegative parameters length compact)
  have nonnegative : 0 ≤ constant := mul_nonneg coefficientNonnegative sourceNonnegative
  have retained (n : ℕ) : originalWeightedRetainedNorm parameters (lower n) length (positive n)
      ((lowerHalf n).trans (by norm_num)) lengthPositive (solves n).ofLp.1 ≤ constant :=
    (fixedExhaustionSolve_retainedBound parameters length compact lengthPositive widthHalf widthLength state small
      (lower n) (positive n) (lowerHalf n) (data n)).trans (mul_le_mul_of_nonneg_left (sourceEstimate n) coefficientNonnegative)
  have source (n k : ℕ) (included : lower n ≤ lower k) :
      originalFullSourceRestriction parameters (lower n) (lower k) included (solves n).ofLp.2 = sources k :=
    sourceCompatible n k included
  exact originalCompatibleEquationFamily_of_bounded_sequence parameters length compact lengthPositive widthHalf widthLength state small
    lower positive lowerHalf (cofinalRestrictionSequence parameters length lengthPositive lower positive lowerHalf solves)
    (fixedCollarCompactnessConstant parameters length lengthPositive lower positive lowerHalf constant sources)
    (cofinalRestrictionSequence_fullBound parameters length lengthPositive lower positive lowerHalf solves constant nonnegative retained sources source)
    sources 0 constant nonnegative
    (cofinalRestrictionSequence_equations parameters length lengthPositive lower positive lowerHalf solves cofinal compact widthHalf widthLength state small
      (fun n => fixedExhaustionSolve_equation parameters length compact lengthPositive widthHalf widthLength state small
        (lower n) (positive n) (lowerHalf n) (data n)))
    (cofinalRestrictionSequence_sources parameters length lengthPositive lower positive lowerHalf solves cofinal sources source)
    (cofinalRestrictionSequence_fullOuter parameters length lengthPositive lower positive lowerHalf solves cofinal compact state 0
      (fun n => fixedExhaustionSolve_fullOuter parameters length compact lengthPositive widthHalf widthLength state small
        (lower n) (positive n) (lowerHalf n) (data n)))
    (fun k => Eventually.of_forall (cofinalRestrictionSequence_retainedBound parameters length lengthPositive lower positive lowerHalf solves constant nonnegative retained k))
    (cofinalRestrictionSequence_compatible parameters length lengthPositive lower positive lowerHalf solves cofinal)

end Grad.ActualAnnularExhaustion
