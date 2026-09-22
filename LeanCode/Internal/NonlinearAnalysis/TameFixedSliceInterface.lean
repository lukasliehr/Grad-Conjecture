import TameCompositionBound

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.Constraints

/-! # The exact Q21/Q22 interface

The literal fixed-reference nonlinear map `F(p, ε, x) = 𝒵(ε, 𝒮_p(T_{M*,M_p} x))`
on the joint state `(ε, x)`, and the Q22 goal: a genuine iterated
directional derivative tower on the literal Q13 axis ball with, at every
grade `q` and order `j`, on every bounded `X⁴` ball, the exact one-high
estimate — high grade `q + 6` on the base state or on exactly one direction,
grade four on every other direction. Directions carry an `ε` component, so
the `ε`-derivatives of Q23 are included; the finite seed parameters are
fixed. The derivative family is an output; nothing is assumed about it. -/

/-- The literal fixed-reference Q21 map: the literal O14 quotient polynomial
at the scalar and the normalized chart of the transferred reference state. -/
def fixedSliceMap (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (state : JointState parameters) : QuotientRows parameters :=
  quotientPolynomialRows parameters cellLength
    (referenceState parameters reference insideR seed insideS state)

/-- Q22 (with the `ε`-directions of Q23): the literal fixed-reference map has
a genuine iterated directional derivative tower on the literal Q13 axis ball,
with the exact loss-six one-high bound at every grade and order on every
bounded `X⁴` ball. -/
def FixedSliceDerivativeGoal : Prop :=
  ∀ (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain),
    ∃ derivative : (order : ℕ) → JointState parameters →
        (Fin order → JointState parameters) → QuotientRows parameters,
      (∀ state, derivative 0 state (fun position => position.elim0) =
        fixedSliceMap parameters cellLength reference insideR seed insideS state) ∧
      (∀ (order : ℕ) (base : JointState parameters)
        (directions : Fin (order + 1) → JointState parameters),
        ChartAxisCondition base.2 →
        IsJointRowsDirectionalDerivative
          (fun state => derivative order state
            (fun position => directions position.castSucc))
          base (directions (Fin.last order)) (derivative (order + 1) base directions)) ∧
      ∀ (grade order : ℕ) (bound : ℝ), ∃ constant : ℝ, 0 ≤ constant ∧
        ∀ (base : JointState parameters) (directions : Fin order → JointState parameters),
          ChartAxisCondition base.2 →
          jointNorm 4 base ≤ bound →
          rowsGradeNorm grade (derivative order base directions) ≤
            constant * ((1 + jointNorm (grade + 6) base) *
              ∏ position, jointNorm 4 (directions position) +
              ∑ position, jointNorm (grade + 6) (directions position) *
                ∏ other ∈ Finset.univ.erase position, jointNorm 4 (directions other))

end Grad.NonlinearQuotientBounds
