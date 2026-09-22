import AKM6SameOriginalResponseLinear

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open Set Filter
open scoped Topology
namespace Grad.AnnularWeakExhaustion
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularStrongOrbit
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularFullGraph
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularForwardDatum Grad.AnnularForwardTraces
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule

local instance weakOriginalDataRealNormed (parameters : PhaseParameters) (lower : ℝ) :
    NormedSpace ℝ (OriginalStrongCarrier parameters lower 0 0) := inferInstance
local instance weakOriginalDataRealModule (parameters : PhaseParameters) (lower : ℝ) :
    Module ℝ (OriginalStrongCarrier parameters lower 0 0) :=
  (weakOriginalDataRealNormed parameters lower).toModule

attribute [local instance] sourceRadialRealInner sourceGraphRealInner sourceKnownGraphRealInner
  weakRetainedRealInner weakSourcesRealInner weakFiveRealInner

private theorem rangeFixedPoint {D E : Type*} (solve : D → E) (forward : E → D)
    (leftInverse : Function.LeftInverse forward solve) (field : E) :
    solve (forward field) = field ↔ field ∈ range solve := by
  constructor
  · intro same
    exact ⟨forward field, same⟩
  · rintro ⟨data, rfl⟩
    exact congrArg solve (leftInverse data)

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
include small

/-- The actual solution and its unchanged four source/residual blocks. -/
def sameOriginalFiveLinear : OriginalStrongCarrier parameters lower 0 0 →L[ℝ]
    OriginalFiveBlockAmbient parameters lower length positive :=
  forwardHilbertPair (D := OriginalStrongCarrier parameters lower 0 0)
    (E := OriginalCoupledSpace lower length positive) (F := OriginalFullSourceBlocks parameters lower)
    (sameOriginalResponseLinear parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small)
    (forwardHilbertFirst.comp (OriginalStrongCarrier parameters lower 0 0).subtypeL)

theorem sameOriginalFiveLinear_apply (data : OriginalStrongCarrier parameters lower 0 0) :
    sameOriginalFiveLinear parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data =
    originalSolvedFiveBlock parameters length compact lower positive lowerHalf lengthPositive state
      widthHalf widthLength small data := by
  change WithLp.toLp 2
    (sameOriginalResponseLinear parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data, data.val.ofLp.1) = _
  rw [sameOriginalResponseLinear_apply]
  rfl

/-- This bounded projection has exactly the genuine original observed
equation graph as fixed points; no smoothness condition defines it. -/
def originalEquationProjection : OriginalFiveBlockAmbient parameters lower length positive →L[ℝ]
    OriginalFiveBlockAmbient parameters lower length positive :=
  (sameOriginalFiveLinear parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small).comp
    (originalForwardDatum parameters length compact lower positive lowerHalf lengthPositive state)

theorem originalEquationProjection_fixed_iff
    (field : OriginalFiveBlockAmbient parameters lower length positive) :
    originalEquationProjection parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small field = field ↔
    field ∈ OriginalObservedEquationGraph parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state := by
  let solve := originalSolvedFiveBlock parameters length compact lower positive lowerHalf lengthPositive state
    widthHalf widthLength small
  let forward := originalForwardDatum parameters length compact lower positive lowerHalf lengthPositive state
  have same : originalEquationProjection parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small field = solve (forward field) :=
    sameOriginalFiveLinear_apply parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small (forward field)
  have fixed := rangeFixedPoint solve forward
    (originalForwardDatum_leftInverse parameters length compact lower positive lowerHalf lengthPositive state
      widthHalf widthLength small) field
  have rangeSame := originalObservedEquationGraph_eq_range parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small
  exact (Iff.of_eq (congrArg (fun value => value = field) same)).trans
    (fixed.trans (Iff.of_eq (congrArg (fun set => field ∈ set) rangeSame.symm)))

/-- Genuine original equations persist under weak convergence of all five
blocks, including when the equations hold only along the eventual tail. -/
theorem originalObservedEquationGraph_weak_limit
    {sequence : ℕ → OriginalFiveBlockAmbient parameters lower length positive}
    {limit : OriginalFiveBlockAmbient parameters lower length positive}
    (convergence : WeakConverges sequence limit)
    (equations : ∀ᶠ n in atTop, sequence n ∈
      OriginalObservedEquationGraph parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state) :
    limit ∈ OriginalObservedEquationGraph parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state := by
  apply (originalEquationProjection_fixed_iff parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small limit).mp
  apply weakLimit_comparison convergence convergence
    (originalEquationProjection parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small)
  filter_upwards [equations] with n hn
  exact (originalEquationProjection_fixed_iff parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small (sequence n)).mpr hn

end Grad.AnnularWeakExhaustion
