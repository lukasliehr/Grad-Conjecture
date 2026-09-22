import AKP3ActualCofinalRestrictionSequence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.ActualAnnularExhaustion
open Grad.CartesianState Grad.AnnularFullGraph Grad.AnnularForwardDatum Grad.AnnularStrongOrbit
open Grad.AnnularForwardTraces Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularRestriction
open Grad.AnnularExhaustionEstimate Grad.AnnularWeakExhaustion Grad.ActualBoundaryPrimitives
open Grad.GaugeCoefficients.Physical.Allocation
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule

variable (parameters : PhaseParameters) (length : ℝ) (lengthPositive : 0 < length)
    (lower : ℕ → ℝ) (positive : ∀ n, 0 < lower n) (lowerHalf : ∀ n, lower n ≤ 1 / 2)
    (field : ∀ n, OriginalFiveBlockAmbient parameters (lower n) length (positive n))

def fixedCollarCompactnessConstant (constant : ℝ)
    (sources : ∀ k, OriginalFullSourceBlocks parameters (lower k)) (collar : ℕ) : ℝ :=
  ‖(originalCoupledEquivalence parameters (lower collar) length (positive collar)
    ((lowerHalf collar).trans (by norm_num)) lengthPositive).symm.toContinuousLinearMap‖ * constant + ‖sources collar‖

theorem cofinalRestrictionSequence_fullBound (constant : ℝ) (nonnegative : 0 ≤ constant)
    (estimate : ∀ n, originalWeightedRetainedNorm parameters (lower n) length (positive n)
      ((lowerHalf n).trans (by norm_num)) lengthPositive (field n).ofLp.1 ≤ constant)
    (sources : ∀ k, OriginalFullSourceBlocks parameters (lower k))
    (same : ∀ n k (included : lower n ≤ lower k),
      originalFullSourceRestriction parameters (lower n) (lower k) included (field n).ofLp.2 = sources k)
    (collar stage : ℕ) :
    ‖cofinalRestrictionSequence parameters length lengthPositive lower positive lowerHalf field collar stage‖ ≤
      fixedCollarCompactnessConstant parameters length lengthPositive lower positive lowerHalf constant sources collar := by
  have native := cofinalRestrictionSequence_retainedBound parameters length lengthPositive lower positive lowerHalf field constant nonnegative estimate collar stage
  by_cases included : lower stage ≤ lower collar
  · have source : (cofinalRestrictionSequence parameters length lengthPositive lower positive lowerHalf field collar stage).ofLp.2 = sources collar := by
      rw [cofinalRestrictionSequence_of_included parameters length lengthPositive lower positive lowerHalf field collar stage included]
      exact same stage collar included
    have fixed := originalFiveBlock_fixedCollarBound parameters (lower collar) length (positive collar)
      ((lowerHalf collar).trans (by norm_num)) lengthPositive _ constant native
    rw [source] at fixed
    exact fixed
  · simp only [cofinalRestrictionSequence, dif_neg included,norm_zero]
    exact add_nonneg (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) nonnegative) (norm_nonneg _)

variable (cofinal : ∀ k, ∀ᶠ n in atTop, lower n ≤ lower k)
    (compact : ℝ) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact)

include cofinal
include small in
 theorem cofinalRestrictionSequence_equations
    (equations : ∀ n, field n ∈ OriginalObservedEquationGraph parameters length compact (lower n) (positive n)
      (lowerHalf n) lengthPositive widthHalf widthLength state)
    (collar : ℕ) :
    ∀ᶠ n in atTop, cofinalRestrictionSequence parameters length lengthPositive lower positive lowerHalf field collar n ∈
      OriginalObservedEquationGraph parameters length compact (lower collar) (positive collar) (lowerHalf collar)
        lengthPositive widthHalf widthLength state := by
  filter_upwards [cofinal collar] with n included
  rw [cofinalRestrictionSequence_of_included parameters length lengthPositive lower positive lowerHalf field collar n included]
  exact restrictedOriginalEquationGraph parameters length compact (lower n) (lower collar) (positive n) (positive collar)
    (lowerHalf collar) lengthPositive included widthHalf widthLength state small (field n) (equations n)

omit widthHalf widthLength small in
 theorem cofinalRestrictionSequence_fullOuter
    (outer : HighBoundaryPrimitive parameters 0 0)
    (boundary : ∀ n, originalOuterBoundaryTrace parameters length compact (lower n) (positive n) (lowerHalf n) lengthPositive state
      ((field n).ofLp.1,(field n).ofLp.2.ofLp.1) = outer)
    (collar : ℕ) :
    ∀ᶠ n in atTop,
      let point := cofinalRestrictionSequence parameters length lengthPositive lower positive lowerHalf field collar n
      originalOuterBoundaryTrace parameters length compact (lower collar) (positive collar) (lowerHalf collar) lengthPositive state
        (point.ofLp.1,point.ofLp.2.ofLp.1) = outer := by
  filter_upwards [cofinal collar] with n included
  dsimp only
  rw [cofinalRestrictionSequence_of_included parameters length lengthPositive lower positive lowerHalf field collar n included]
  exact (originalRetainedRestriction_fullOuter (lower n) (lower collar) length (positive n) (positive collar)
    (lowerHalf collar) included parameters lengthPositive compact state (field n).ofLp.1 (field n).ofLp.2.ofLp.1).trans (boundary n)

end Grad.ActualAnnularExhaustion
