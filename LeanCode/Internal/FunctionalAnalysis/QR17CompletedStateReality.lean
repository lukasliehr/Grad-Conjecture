import QR16StateReality
import CQ2CompletedProjection

noncomputable section

namespace Grad.CompletedReality

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.SmoothingFamily Grad.Cor18
open Grad.AxisCore

/-- The literal smooth commutation transfers to the actual completed state
projection by the accepted original-core density theorem. -/
theorem completedStateProjection_conjugate (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (grade : ℕ) (completed : XAmbient parameters grade →L[ℂ] XAmbient parameters grade)
    (coreEquation : ∀ field, completed (stateToGrade parameters grade field) =
      stateToGrade parameters grade (fullProjection parameters parameter inside field))
    (point : XAmbient parameters grade) :
    xConjugation parameters grade (completed point) =
      completed (xConjugation parameters grade point) := by
  refine isClosed_property (stateToGrade_denseRange parameters grade)
    (isClosed_eq ((xConjugation parameters grade).continuous.comp completed.continuous)
      (completed.continuous.comp (xConjugation parameters grade).continuous)) ?_ point
  intro field
  dsimp only [Function.comp_apply]
  rw [coreEquation, xConjugation_eta, xConjugation_eta, coreEquation,
    fullProjection_conjugate]

/-- Actual COR19 projection with its newly proved COR22 intertwining law. -/
theorem actualCompletedStateReality (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 3 ≤ grade) :
    ∃ completed : XAmbient parameters grade →L[ℂ] XAmbient parameters grade,
      ∃ constant : ℝ, 0 ≤ constant ∧
        (∀ field, completed (stateToGrade parameters grade field) =
          stateToGrade parameters grade (fullProjection parameters parameter inside field)) ∧
        (∀ point, ‖completed point‖ ≤ constant * ‖point‖) ∧
        (∀ point, completed (completed point) = completed point) ∧
        (∀ point, xConjugation parameters grade (completed point) =
          completed (xConjugation parameters grade point)) ∧
        (∀ other : XAmbient parameters grade →L[ℂ] XAmbient parameters grade,
          (∀ field, other (stateToGrade parameters grade field) =
            stateToGrade parameters grade (fullProjection parameters parameter inside field)) →
          other = completed) := by
  obtain ⟨completed, constant, positive, _, coreEquation, bound, idem, unique⟩ :=
    actualCompletedProjection parameters parameter inside grade large
  exact ⟨completed, constant, positive, coreEquation, bound, idem,
    completedStateProjection_conjugate parameters parameter inside grade completed coreEquation, unique⟩

end Grad.CompletedReality
