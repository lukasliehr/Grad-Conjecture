import AKP7ActualAllGradeAnnularWitnesses

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.ActualAnnularExhaustion
open Grad.CartesianState Grad.AnnularFullGraph Grad.AnnularForwardDatum Grad.AnnularStrongOrbit
open Grad.AnnularForwardTraces Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularCoupledInverse Grad.AnnularHighGenerators Grad.AnnularWeakExhaustion
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule
  sourceRadialRealInner sourceGraphRealInner sourceKnownGraphRealInner
  weakRetainedRealInner weakSourcesRealInner weakFiveRealInner weakWeightedRetainedRealInner

/-- Attach all actual inserted annular witnesses to the already extracted
SAME full original weak limit. The second subsequence preserves that limit. -/
theorem actualCofinal_allGradeLimits
    (parameters : PhaseParameters) (length : ℝ) (lengthPositive : 0 < length)
    (lower : ℕ → ℝ) (positive : ∀ n, 0 < lower n) (lowerHalf : ∀ n, lower n ≤ 1 / 2)
    (cofinal : ∀ k, ∀ᶠ n in atTop, lower n ≤ lower k)
    (field : ∀ n, OriginalFiveBlockAmbient parameters (lower n) length (positive n))
    (limit : ∀ k, OriginalFiveBlockAmbient parameters (lower k) length (positive k))
    (subsequence : ℕ → ℕ) (increasing : StrictMono subsequence)
    (convergence : ∀ k, WeakConverges
      (cofinalRestrictionSequence parameters length lengthPositive lower positive lowerHalf field k ∘ subsequence) (limit k))
    (retained : ∀ (_t : ℕ) n, CoupledSpace (lower n) length (positive n) lengthPositive)
    (actual : ∀ t n, CoupledInsertedGrade (lower n) length (positive n) lengthPositive t
      (originalWeightedRetainedObservation parameters (lower n) length (positive n) ((lowerHalf n).trans (by norm_num)) lengthPositive (field n))
      (retained t n))
    (constant : ℕ → ℝ) (uniform : ∀ t n, ‖retained t n‖ ≤ constant t) :
    ∃ (graded : ∀ k (_t : ℕ), CoupledSpace (lower k) length (positive k) lengthPositive)
      (further : ℕ → ℕ), StrictMono further ∧
      (∀ k, WeakConverges
        (cofinalRestrictionSequence parameters length lengthPositive lower positive lowerHalf field k ∘ (subsequence ∘ further)) (limit k)) ∧
      (∀ k t, CoupledInsertedGrade (lower k) length (positive k) lengthPositive t
        (originalWeightedRetainedObservation parameters (lower k) length (positive k) ((lowerHalf k).trans (by norm_num)) lengthPositive (limit k))
        (graded k t) ∧ ‖graded k t‖ ≤ constant t) := by
  have nonnegative (t : ℕ) : 0 ≤ constant t := (norm_nonneg (retained t 0)).trans (uniform t 0)
  let sequence := fun k => cofinalRestrictionSequence parameters length lengthPositive lower positive lowerHalf field k ∘ subsequence
  let weighted := fun k t => cofinalInsertedSequence length lengthPositive lower positive lowerHalf (retained t) k ∘ subsequence
  have same (k t : ℕ) : ∀ᶠ n in atTop, CoupledInsertedGrade (lower k) length (positive k) lengthPositive t
      (originalWeightedRetainedObservation parameters (lower k) length (positive k) ((lowerHalf k).trans (by norm_num)) lengthPositive (sequence k n))
      (weighted k t n) :=
    increasing.tendsto_atTop.eventually
      (cofinalInsertedSequence_actual length lengthPositive lower positive lowerHalf (retained t) parameters t field (actual t) cofinal k)
  have bound (k t n : ℕ) : ‖weighted k t n‖ ≤ constant t :=
    cofinalInsertedSequence_bound length lengthPositive lower positive lowerHalf (retained t) (constant t) (nonnegative t) (uniform t) k (subsequence n)
  obtain ⟨graded,further,strict,fullWeak,grades⟩ := originalSameAllGrades_weakExtraction parameters length lengthPositive lower positive
    (fun k => (lowerHalf k).trans (by norm_num)) sequence limit convergence weighted same constant bound
  exact ⟨graded,further,strict,fullWeak,fun k t => (grades k t).2⟩

end Grad.ActualAnnularExhaustion
