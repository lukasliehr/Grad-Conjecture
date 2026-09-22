import AKM4SequenceClosedSpanExtraction
import AKJ2OriginalFiveBlockClosedEquationGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
open Set Filter
open scoped Topology
namespace Grad.AnnularWeakExhaustion
open Grad.CartesianState Grad.AnnularFullGraph Grad.AnnularForwardDatum
open Grad.AnnularStrongOrbit Grad.AnnularForwardTraces Grad.AnnularStrongSolution
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule
  sourceRadialRealInner sourceGraphRealInner sourceKnownGraphRealInner

/-- These structures use the unchanged original Hilbert norms. -/
local instance weakRetainedRealInner (lower length : ℝ) (positive : 0 < lower) :
    InnerProductSpace ℝ (OriginalCoupledSpace lower length positive) :=
  InnerProductSpace.rclikeToReal ℂ (OriginalCoupledSpace lower length positive)
local instance weakSourcesRealInner (parameters : PhaseParameters) (lower : ℝ) :
    InnerProductSpace ℝ (OriginalFullSourceBlocks parameters lower) := inferInstance
local instance weakFiveRealInner (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower) :
    InnerProductSpace ℝ (OriginalFiveBlockAmbient parameters lower length positive) := inferInstance

/-- One actual five-block graph limit is extracted simultaneously at all
enumerated annulus/grade pairs. Every copied source and full residual stays
in the Hilbert carrier, and each original bound is retained. -/
theorem originalFiveBlocks_countable_weakExtraction (parameters : PhaseParameters)
    (length : ℝ) (lower : ℕ → ℝ) (positive : ∀ k, 0 < lower k)
    (sequence : ∀ k, ℕ → OriginalFiveBlockAmbient parameters (lower k) length (positive k))
    (constant : ℕ → ℝ) (bounded : ∀ k n, ‖sequence k n‖ ≤ constant k) :
    ∃ (limit : ∀ k, OriginalFiveBlockAmbient parameters (lower k) length (positive k))
      (subsequence : ℕ → ℕ), StrictMono subsequence ∧
      ∀ k, ‖limit k‖ ≤ constant k ∧ WeakConverges (sequence k ∘ subsequence) (limit k) :=
  countableHilbert_weakExtraction
    (fun k => OriginalFiveBlockAmbient parameters (lower k) length (positive k)) sequence constant bounded

end Grad.AnnularWeakExhaustion
