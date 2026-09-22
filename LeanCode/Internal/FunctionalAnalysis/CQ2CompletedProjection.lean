import CQ1DenseExtension

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Cor18

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.Constraints.Gauges Grad.SmoothingFamily Grad.ImplementationReadiness Grad.AxisCore

/-! # COR19: the completed full-domain projection `P_{M,q}` on `XAmbient q`

For every actual admissible seed and every grade `q ≥ 3`, the accepted COR18
smooth-core projection extends through the COR17 dense isometric embedding
`stateToGrade` to a continuous linear projection of the completed carrier
with the exact smooth-core equation, the same bound, and `P_{M,q}² = P_{M,q}`.
The general dense-core bounded-idempotent extension lemma is packaged as
`dense_core_projection_extension`. -/

def CompletedProjectionGoal : Prop :=
  ∀ (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ), 3 ≤ grade →
    ∃ (completed : XAmbient parameters grade →L[ℂ] XAmbient parameters grade) (constant : ℝ),
      0 ≤ constant ∧
      (∀ state : StateCore parameters,
        ‖stateToGrade parameters grade (fullProjection parameters parameter inside state)‖ ≤
          constant * ‖stateToGrade parameters grade state‖) ∧
      (∀ state : StateCore parameters,
        completed (stateToGrade parameters grade state) =
          stateToGrade parameters grade (fullProjection parameters parameter inside state)) ∧
      (∀ point : XAmbient parameters grade, ‖completed point‖ ≤ constant * ‖point‖) ∧
      (∀ point : XAmbient parameters grade, completed (completed point) = completed point) ∧
      (∀ other : XAmbient parameters grade →L[ℂ] XAmbient parameters grade,
        (∀ state : StateCore parameters, other (stateToGrade parameters grade state) =
          stateToGrade parameters grade (fullProjection parameters parameter inside state)) →
        other = completed)

/-- COR19: the completed projection goal holds. -/
theorem actualCompletedProjection : CompletedProjectionGoal := by
  intro parameters parameter inside grade gradeLarge
  obtain ⟨constant, nonneg, coreBound⟩ :=
    fullProjection_norm_le parameters parameter inside grade gradeLarge
  obtain ⟨completed, coreEq, bound, idempotent, unique⟩ :=
    dense_core_projection_extension (stateToGrade parameters grade)
      (stateToGrade_injective parameters grade) (stateToGrade_denseRange parameters grade)
      (fullProjection parameters parameter inside) constant nonneg coreBound
      (fullProjection_idempotent parameters parameter inside)
  exact ⟨completed, constant, nonneg, coreBound, coreEq, bound, idempotent, unique⟩

end Grad.Cor18
