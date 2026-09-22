import QS4Goal

noncomputable section

namespace Grad.RealFixedRanges

open Grad.CartesianState Grad.Constraints Grad.AxisCore Grad.SmoothingFamily
open Grad.QuotientProjection

/-- COR24 approximation-error input, in the inherited original state norm.
Existence of the real projected approximants remains the COR24 obligation. -/
theorem stateApproximation_error (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (approximation : stateSmoothRange parameters parameter inside)
    (target : stateRange parameters parameter inside grade large) :
    dist (stateSmoothEmbedding parameters parameter inside grade large approximation) target =
      ‖stateToGrade parameters grade approximation.val - target.val‖ := by
  rw [dist_eq_norm]
  rfl

/-- COR24 quotient approximation-error input: the literal fourfold Hilbert
distance, not a maximum norm or a surrogate quotient norm. -/
theorem sourceApproximation_error (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade)
    (approximation : sourceSmoothRange parameters) (target : sourceRange parameters grade large) :
    dist (sourceSmoothEmbedding parameters grade large approximation) target =
      ‖quotientEta parameters grade approximation.val - target.val‖ := by
  rw [dist_eq_norm]
  rfl

/-- Closed/completed actual carriers can now be used by the downstream Banach
calculus, without assuming an unconstructed constrained completion. -/
example (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    CompleteSpace (stateRange parameters parameter inside grade large) ∧
      CompleteSpace (sourceRange parameters grade large) :=
  ⟨(actualRealFixedRanges parameters parameter inside grade large).2.2.1,
    (actualRealFixedRanges parameters parameter inside grade large).2.2.2.1⟩

end Grad.RealFixedRanges
