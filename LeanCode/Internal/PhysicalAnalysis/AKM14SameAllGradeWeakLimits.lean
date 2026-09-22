import AKM11ActualInsertedGradeWeakClosure
import AKM12CompatibleOriginalEquationFamily
import AKM13DoubleCountableWeakExtraction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.AnnularWeakExhaustion
open Grad.CartesianState Grad.AnnularFullGraph Grad.AnnularForwardDatum Grad.AnnularStrongOrbit
open Grad.AnnularForwardTraces Grad.AnnularStrongSolution Grad.AnnularExhaustionEstimate
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule
  sourceRadialRealInner sourceGraphRealInner sourceKnownGraphRealInner
  weakRetainedRealInner weakSourcesRealInner weakFiveRealInner weakWeightedRetainedRealInner

/-- Refine the one full original graph limit by a common subsequence for all
actual inserted grades on all collars. The limit fields are unchanged, and
each retained grade bound survives with exactly the supplied constant. -/
theorem originalSameAllGrades_weakExtraction
    (parameters : PhaseParameters) (length : ℝ) (lengthPositive : 0 < length)
    (lower : ℕ → ℝ) (positive : ∀ k, 0 < lower k) (bounded : ∀ k, lower k ≤ 1)
    (sequence : ∀ k, ℕ → OriginalFiveBlockAmbient parameters (lower k) length (positive k))
    (limit : ∀ k, OriginalFiveBlockAmbient parameters (lower k) length (positive k))
    (convergence : ∀ k, WeakConverges (sequence k) (limit k))
    (inserted : ∀ k (_t : ℕ), ℕ → CoupledSpace (lower k) length (positive k) lengthPositive)
    (actual : ∀ k t, ∀ᶠ n in atTop, CoupledInsertedGrade (lower k) length (positive k) lengthPositive t
      (originalWeightedRetainedObservation parameters (lower k) length (positive k) (bounded k) lengthPositive (sequence k n))
      (inserted k t n))
    (constant : ℕ → ℝ) (uniform : ∀ k t n, ‖inserted k t n‖ ≤ constant t) :
    ∃ (graded : ∀ k (_t : ℕ), CoupledSpace (lower k) length (positive k) lengthPositive)
      (subsequence : ℕ → ℕ), StrictMono subsequence ∧
      (∀ k, WeakConverges (sequence k ∘ subsequence) (limit k)) ∧
      (∀ k t, WeakConverges (inserted k t ∘ subsequence) (graded k t) ∧
        CoupledInsertedGrade (lower k) length (positive k) lengthPositive t
          (originalWeightedRetainedObservation parameters (lower k) length (positive k) (bounded k) lengthPositive (limit k))
          (graded k t) ∧ ‖graded k t‖ ≤ constant t) := by
  obtain ⟨graded, subsequence, increasing, grades⟩ := doubleCountableHilbert_weakExtraction
    (fun k _ => CoupledSpace (lower k) length (positive k) lengthPositive) inserted (fun _ t => constant t) uniform
  refine ⟨graded, subsequence, increasing, fun k => (convergence k).subsequence subsequence increasing, ?_⟩
  intro k t
  refine ⟨(grades k t).2, ?_, (grades k t).1⟩
  exact coupledInsertedGrade_weak_limit (lower k) length (positive k) lengthPositive t
    (((convergence k).subsequence subsequence increasing).map
      (originalWeightedRetainedObservation parameters (lower k) length (positive k) (bounded k) lengthPositive))
    (grades k t).2 (increasing.tendsto_atTop.eventually (actual k t))

end Grad.AnnularWeakExhaustion
