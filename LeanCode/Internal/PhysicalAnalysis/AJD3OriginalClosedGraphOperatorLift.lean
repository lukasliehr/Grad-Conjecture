import AJD1RealToComplexOperatorRetraction

noncomputable section
set_option autoImplicit false
namespace Grad.AnnularCrossOrbit

private theorem linearSmoothComposition {P A B : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (mapping : A →L[ℝ] B)
    (order : WithTop ℕ∞) (function : P → A) (smooth : ContDiff ℝ order function) :
    ContDiff ℝ order (fun point => mapping (function point)) := mapping.contDiff.comp smooth

private theorem linearDerivativeComposition {P A B : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (mapping : A →L[ℝ] B)
    (function : P → A) (derivative : P →L[ℝ] A) (point : P)
    (actual : HasFDerivAt function derivative point) :
    HasFDerivAt (fun tau => mapping (function tau)) (mapping.comp derivative) point :=
  mapping.hasFDerivAt.comp point actual

variable {X E P : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (graph : Submodule ℂ E) [graph.HasOrthogonalProjection]

/-- Fixed bounded projection of an ambient operator into the original closed Hilbert graph. -/
def graphOperatorProjection : (X →L[ℂ] E) →L[ℝ] (X →L[ℂ] graph) :=
  ((ContinuousLinearMap.compL ℂ X E graph) graph.orthogonalProjectionOnto).restrictScalars ℝ

theorem graphOperatorProjection_retract (mapping : X →L[ℂ] graph) :
    graphOperatorProjection graph (graph.subtypeL.comp mapping) = mapping := by
  apply ContinuousLinearMap.ext
  intro field
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (mapping field)

theorem graphOperatorProjection_bound (mapping : X →L[ℂ] E) :
    ‖graphOperatorProjection graph mapping‖ ≤ ‖mapping‖ := by
  have composition := ContinuousLinearMap.opNorm_comp_le graph.orthogonalProjectionOnto mapping
  exact composition.trans ((mul_le_mul_of_nonneg_right graph.orthogonalProjectionOnto_norm_le
    (norm_nonneg mapping)).trans_eq (one_mul _))

variable [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Genuine graph-valued smoothness follows from the SAME operator's ambient coordinates. -/
theorem graphOperator_contDiff_of_inclusion (order : WithTop ℕ∞) (family : P → X →L[ℂ] graph)
    (smooth : ContDiff ℝ order (fun point => graph.subtypeL.comp (family point))) :
    ContDiff ℝ order family := by
  have composed := linearSmoothComposition (A := X →L[ℂ] E) (B := X →L[ℂ] graph) (graphOperatorProjection (X := X) graph) order _ smooth
  simpa only [Function.comp_def, graphOperatorProjection_retract] using composed

theorem graphOperator_hasFDerivAt_of_inclusion (family : P → X →L[ℂ] graph)
    (derivative : P →L[ℝ] (X →L[ℂ] E)) (point : P)
    (actual : HasFDerivAt (fun tau => graph.subtypeL.comp (family tau)) derivative point) :
    HasFDerivAt family ((graphOperatorProjection graph).comp derivative) point := by
  have composed := linearDerivativeComposition (A := X →L[ℂ] E) (B := X →L[ℂ] graph) (graphOperatorProjection (X := X) graph) _ derivative point actual
  simpa only [Function.comp_def, graphOperatorProjection_retract] using composed

end Grad.AnnularCrossOrbit
