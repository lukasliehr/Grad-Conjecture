import QR7CompletedQuotientReality

noncomputable section

namespace Grad.CompletedReality

open Grad.ClosedJets Grad.CartesianState Grad.AxisCore Grad.QuotientProjection
open Grad.SmoothingFamily

/-- Exact consumer of the ordinary state and swapped quotient completed maps. -/
theorem completedRealInvolutions (parameters : PhaseParameters) (grade : ℕ) :
    Function.Involutive (xConjugation parameters grade) ∧
      Function.Involutive (zConjugation parameters grade) ∧
      (∀ point : XAmbient parameters grade, ‖xConjugation parameters grade point‖ = ‖point‖) ∧
      (∀ point : ZAmbient parameters grade, ‖zConjugation parameters grade point‖ = ‖point‖) :=
  ⟨xConjugation_involutive parameters grade, zConjugation_involutive parameters grade,
    (xConjugation parameters grade).norm_map, (zConjugation parameters grade).norm_map⟩

/-- A consumer needing an actual bounded quotient projection preserving real
elements obtains it from COR21 and the proved literal intertwining, without
postulating any projection or real-preservation property. -/
theorem realQuotientProjection_exists (parameters : PhaseParameters)
    (grade : ℕ) (large : 3 ≤ grade) :
    ∃ completed : ZAmbient parameters grade →L[ℂ] ZAmbient parameters grade,
      (∀ field, completed (quotientEta parameters grade field) =
        quotientEta parameters grade (quotientProjection parameters field)) ∧
      (∀ point, completed (completed point) = completed point) ∧
      (∀ point, zConjugation parameters grade point = point →
        zConjugation parameters grade (completed point) = completed point) := by
  obtain ⟨_, _, completed, coreEquation, _, idem, commutes, _⟩ :=
    actualCompletedQuotientReality parameters grade large
  refine ⟨completed, coreEquation, idem, ?_⟩
  intro point realPoint
  rw [commutes, realPoint]

end Grad.CompletedReality
