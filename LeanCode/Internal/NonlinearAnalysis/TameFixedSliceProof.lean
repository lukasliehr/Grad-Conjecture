import TameFixedSliceInterface

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.Constraints

/-! # Q22, assembled

The composed derivative family of the literal quotient polynomial with the
inner map `(ε, x) ↦ (ε, 𝒮_p(T x))` witnesses the fixed-slice derivative goal:
order zero is the literal map, every order differentiates genuinely to the
next along the newest direction on the literal Q13 ball (the finite
set-partition chain rule), and every order obeys the exact one-high
loss-six bound on every bounded `X⁴` ball. -/

/-- The fixed-slice derivative family: the composed family of the literal
polynomial with the inner reference family. -/
def fixedSliceDerivative (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) :
    (order : ℕ) → JointState parameters → (Fin order → JointState parameters) →
      QuotientRows parameters :=
  composedDerivative (referenceFamily parameters reference insideR seed insideS) cellLength

/-- Q22: the fixed-slice derivative goal holds. -/
theorem actualFixedSliceDerivative : FixedSliceDerivativeGoal := by
  intro parameters cellLength reference insideR seed insideS
  refine ⟨fixedSliceDerivative parameters cellLength reference insideR seed insideS, ?_, ?_, ?_⟩
  · intro state
    unfold fixedSliceDerivative
    rw [composedDerivative_zeroth, referenceFamily_zeroth]
    rfl
  · intro order base directions axis
    exact composedDerivative_genuine (referenceFamily parameters reference insideR seed insideS)
      (fun state => ChartAxisCondition state.2)
      (fun order base directions admissible =>
        referenceFamily_genuine reference insideR seed insideS order base directions admissible)
      cellLength order base directions axis
  · intro grade order bound
    obtain ⟨constant, nonneg, estimate⟩ :=
      composedDerivative_bound (referenceFamily parameters reference insideR seed insideS)
        (fun state => ChartAxisCondition state.2)
        (fun grade count => referenceFamily_bound reference insideR seed insideS grade count)
        cellLength grade order bound
    exact ⟨constant, nonneg, fun base directions axis inBall =>
      estimate base directions axis inBall⟩

end Grad.NonlinearQuotientBounds
