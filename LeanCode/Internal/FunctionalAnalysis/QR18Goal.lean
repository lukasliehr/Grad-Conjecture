import QR17CompletedStateReality

noncomputable section

namespace Grad.CompletedReality

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.SmoothingFamily
open Grad.AxisCore Grad.Cor18 Grad.QuotientProjection

/-- The complete COR22 statement on the actual original-width carriers.
The fixed concrete real maps retain their proved norm, involution and core
laws; the actual complex projections have the exact dense-core equations,
bounds, idempotence, uniqueness, and both real intertwining identities. -/
def CompletedRealityGoal : Prop :=
  (∀ (parameters : PhaseParameters) (dimension grade : ℕ),
    Function.Involutive (aGradeConjugation parameters dimension grade) ∧
    Function.Involutive (axisConjugation parameters dimension grade) ∧
    (∀ field, ‖aGradeConjugation parameters dimension grade field‖ = ‖field‖) ∧
    (∀ field, ‖axisConjugation parameters dimension grade field‖ = ‖field‖) ∧
    (∀ field : GradeCore parameters dimension grade,
      aGradeConjugation parameters dimension grade (aGradeEta parameters field) =
        aGradeEta parameters (gradeCoreConjugation parameters field)) ∧
    (∀ field : Grad.SmoothingFamily.AxisCore parameters.sigma0 (ComplexEuclidean dimension),
      axisConjugation parameters dimension grade (axisToGrade parameters.sigma0 grade field) =
        axisToGrade parameters.sigma0 grade (smoothAxisConjugation parameters dimension field))) ∧
  (∀ (parameters : PhaseParameters) (grade : ℕ),
    Function.Involutive (xConjugation parameters grade) ∧
    Function.Involutive (zConjugation parameters grade) ∧
    (∀ field, ‖xConjugation parameters grade field‖ = ‖field‖) ∧
    (∀ field, ‖zConjugation parameters grade field‖ = ‖field‖) ∧
    (∀ field, xConjugation parameters grade (stateToGrade parameters grade field) =
      stateToGrade parameters grade (xCoreConjugation parameters field)) ∧
    (∀ field, zConjugation parameters grade (quotientEta parameters grade field) =
      quotientEta parameters grade (zCoreConjugation parameters field))) ∧
  (∀ (parameters : PhaseParameters) (parameter : Seed.Parameters)
      (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ), 3 ≤ grade →
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
          other = completed)) ∧
  (∀ (parameters : PhaseParameters) (grade : ℕ), 3 ≤ grade →
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∃ completed : ZAmbient parameters grade →L[ℂ] ZAmbient parameters grade,
        (∀ field, completed (quotientEta parameters grade field) =
          quotientEta parameters grade (quotientProjection parameters field)) ∧
        (∀ point, ‖completed point‖ ≤ constant * ‖point‖) ∧
        (∀ point, completed (completed point) = completed point) ∧
        (∀ point, zConjugation parameters grade (completed point) =
          completed (zConjugation parameters grade point)) ∧
        (∀ other : ZAmbient parameters grade →L[ℂ] ZAmbient parameters grade,
          (∀ field, other (quotientEta parameters grade field) =
            quotientEta parameters grade (quotientProjection parameters field)) →
          other = completed))

end Grad.CompletedReality
