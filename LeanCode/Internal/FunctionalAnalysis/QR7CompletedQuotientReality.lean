import QR6QuotientReality

noncomputable section

namespace Grad.CompletedReality

open Grad.ClosedJets Grad.CartesianState Grad.AxisCore Grad.QuotientProjection

theorem zConjugation_quotientEta (parameters : PhaseParameters) (grade : ℕ)
    (field : SmoothQuotient parameters) :
    zConjugation parameters grade (quotientEta parameters grade field) =
      quotientEta parameters grade (zCoreConjugation parameters field) :=
  zConjugation_eta parameters grade field

/-- Density transfers the literal, swapped smooth-core commutation to the
actual completed quotient projection. No completed commutation is assumed. -/
theorem completedQuotientProjection_conjugate (parameters : PhaseParameters)
    (grade : ℕ) (completed : ZAmbient parameters grade →L[ℂ] ZAmbient parameters grade)
    (coreEquation : ∀ field, completed (quotientEta parameters grade field) =
      quotientEta parameters grade (quotientProjection parameters field))
    (point : ZAmbient parameters grade) :
    zConjugation parameters grade (completed point) =
      completed (zConjugation parameters grade point) := by
  refine isClosed_property (quotientEta_denseRange parameters grade)
    (isClosed_eq ((zConjugation parameters grade).continuous.comp completed.continuous)
      (completed.continuous.comp (zConjugation parameters grade).continuous)) ?_ point
  intro field
  dsimp only [Function.comp_apply]
  rw [coreEquation, zConjugation_quotientEta, zConjugation_quotientEta, coreEquation,
    quotientProjection_conjugate]

/-- The COR22 quotient prerequisite: the actual bounded idempotent from COR21
commutes with the norm-preserving, cell-reversing, spin-swapped real involution.
This theorem does not assert the separate state-projection intertwining. -/
theorem actualCompletedQuotientReality (parameters : PhaseParameters)
    (grade : ℕ) (large : 3 ≤ grade) :
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
          other = completed) := by
  obtain ⟨constant, positive, completed, coreEquation, bound, idem, unique⟩ :=
    completedQuotientProjection_exists parameters grade large
  exact ⟨constant, positive, completed, coreEquation, bound, idem,
    completedQuotientProjection_conjugate parameters grade completed coreEquation, unique⟩

end Grad.CompletedReality
