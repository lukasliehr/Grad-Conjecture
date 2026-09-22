import QuotientDerivativeBound

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct

/-- The explicit `Π w = 0` gauge of the accepted literal-rows domain, now at
the original coefficient-core level: the zero angular mode of the potential
vanishes.  This is an explicit hypothesis, never inferred from any supplied
`CellSolutionFamily` data. -/
def GaugeState (parameters : PhaseParameters) (state : QuotientState parameters) : Prop :=
  angularCore parameters 0 (statePotential state) = 0

/-- Q4: the literal O14 degree-four polynomial on the explicit `Π w = 0`
subspace, with genuine all iterated directional derivatives, exact low
grade-four and high grade-`q+6` one-high bounds on every bounded low ball,
and derivative zero for every order above four.  The derivative family is an
output; nothing is assumed about it. -/
def PolynomialQuotientDerivativeGoal : Prop :=
  ∀ (parameters : PhaseParameters) (cellLength : ℝ),
    ∃ derivative : (order : ℕ) → QuotientState parameters →
        (Fin order → QuotientState parameters) → QuotientRows parameters,
      (∀ state, derivative 0 state (fun position => position.elim0) =
        quotientPolynomialRows parameters cellLength state) ∧
      (∀ (order : ℕ) (base : QuotientState parameters)
        (directions : Fin (order + 1) → QuotientState parameters),
        GaugeState parameters base →
        (∀ position, GaugeState parameters (directions position)) →
        IsRowsDirectionalDerivative
          (fun state => derivative order state
            (fun position => directions position.castSucc))
          base (directions (Fin.last order)) (derivative (order + 1) base directions)) ∧
      (∀ (order : ℕ) (base : QuotientState parameters)
        (directions : Fin order → QuotientState parameters), 4 < order →
        derivative order base directions = 0) ∧
      ∀ (boundGrade order : ℕ) (bound : ℝ), ∃ constant : ℝ, 0 ≤ constant ∧
        ∀ (base : QuotientState parameters)
          (directions : Fin order → QuotientState parameters),
          GaugeState parameters base →
          (∀ position, GaugeState parameters (directions position)) →
          stateNorm 4 base ≤ bound →
          rowsGradeNorm boundGrade (derivative order base directions) ≤
            constant * ((1 + stateNorm (boundGrade + 6) base) *
              ∏ position, stateNorm 4 (directions position) +
              ∑ position, stateNorm (boundGrade + 6) (directions position) *
                ∏ other ∈ Finset.univ.erase position, stateNorm 4 (directions other))

/-- Q4 holds for the actual constructed literal O14 polynomial, with the
exact derivative family `quotientRowsDerivative`. -/
theorem actual_polynomial_quotient_derivative : PolynomialQuotientDerivativeGoal := by
  intro parameters cellLength
  refine ⟨quotientRowsDerivative parameters cellLength, ?_, ?_, ?_, ?_⟩
  · intro state
    exact quotientRowsDerivative_zeroth cellLength state _
  · intro order base directions _ _
    exact quotientRowsDerivative_genuine cellLength order base directions
  · intro order base directions exceeds
    exact quotientRowsDerivative_vanish cellLength order base directions exceeds
  · intro boundGrade order bound
    obtain ⟨constant, nonneg, bounded⟩ := quotientRowsDerivative_bound
      (parameters := parameters) cellLength boundGrade order bound
    exact ⟨constant, nonneg, fun base directions _ _ baseBounded =>
      bounded base directions baseBounded⟩

end Grad.NonlinearQuotientBounds
