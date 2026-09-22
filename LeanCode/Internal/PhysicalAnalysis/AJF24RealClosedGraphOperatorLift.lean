import AJF21FixedDerivativeOperations
import AJD3OriginalClosedGraphOperatorLift

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped ContDiff
namespace Grad.AnnularOrbitGenerators

variable {X E P : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  (graph : Submodule ℂ E) [graph.HasOrthogonalProjection]

/-- The original complex output graph is retained while the prescribed
source is a real Hilbert carrier. -/
def realGraphOperatorProjection : (X →L[ℝ] E) →L[ℝ] (X →L[ℝ] graph) :=
  (ContinuousLinearMap.compL ℝ X E graph) (graph.orthogonalProjectionOnto.restrictScalars ℝ)

theorem realGraphOperatorProjection_retract (mapping : X →L[ℝ] graph) :
    realGraphOperatorProjection graph ((graph.subtypeL.restrictScalars ℝ).comp mapping) = mapping := by
  apply ContinuousLinearMap.ext
  intro field
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (mapping field)

theorem realGraphOperatorProjection_bound (mapping : X →L[ℝ] E) :
    ‖realGraphOperatorProjection graph mapping‖ ≤ ‖mapping‖ := by
  have composed := ContinuousLinearMap.opNorm_comp_le (graph.orthogonalProjectionOnto.restrictScalars ℝ) mapping
  have projection : ‖graph.orthogonalProjectionOnto.restrictScalars ℝ‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.norm_restrictScalars] using graph.orthogonalProjectionOnto_norm_le
  exact composed.trans ((mul_le_mul_of_nonneg_right projection (norm_nonneg mapping)).trans_eq (one_mul _))

variable [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Ambient smoothness of the SAME graph-valued operator gives genuine
smoothness in the original closed graph norm. -/
theorem realGraphOperator_contDiff_of_inclusion (family : P → X →L[ℝ] graph)
    (smooth : ContDiff ℝ ∞ (fun point => (graph.subtypeL.restrictScalars ℝ).comp (family point))) :
    ContDiff ℝ ∞ family := by
  have composed := (ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := X →L[ℝ] E) (F := X →L[ℝ] graph)
    (realGraphOperatorProjection (X := X) graph)).comp smooth
  simpa only [Function.comp_def, realGraphOperatorProjection_retract] using composed

/-- The original graph projection has norm one at every actual derivative. -/
theorem realGraphOperator_iteratedDeriv_bound (family : ℝ → X →L[ℝ] graph)
    (smooth : ContDiff ℝ ∞ (fun point => (graph.subtypeL.restrictScalars ℝ).comp (family point)))
    (order : ℕ) (time : ℝ) :
    ‖iteratedDeriv order family time‖ ≤
      ‖iteratedDeriv order (fun point => (graph.subtypeL.restrictScalars ℝ).comp (family point)) time‖ := by
  have actual := iteratedDeriv_fixedMap (realGraphOperatorProjection (X := X) graph) _ smooth order time
  simp only [realGraphOperatorProjection_retract] at actual
  exact (congrArg norm actual).le.trans (realGraphOperatorProjection_bound graph _)

end Grad.AnnularOrbitGenerators
