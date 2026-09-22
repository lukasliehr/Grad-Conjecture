import PA2PhaseSubadditive

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.PhaseAlgebra

open Grad.CartesianState

/-- The exact FA-phase_algebra-phase goal: for `n, m` in `Z`,
`Phi_r(n+m) <= Phi_r(n) + Phi_r(m)` at every admissible radius. -/
def PhaseSubadditiveGoal : Prop :=
  ∀ (parameters : PhaseParameters) (radius : ℝ), 0 ≤ radius → radius ≤ 1 →
    ∀ n m : ℤ,
      radialPhase parameters radius (n + m) ≤
        radialPhase parameters radius n + radialPhase parameters radius m

/-- The exact FA-phase_algebra-equivalent goal: for every `n`,
`exp(omega |n|) <= exp(Phi_r(n)) <= exp(sigma0 + gamma) exp(omega |n|)`,
and `lambda_n <= mu_n <= sqrt 2 lambda_n`. -/
def PhaseEquivalentGoal : Prop :=
  ∀ (parameters : PhaseParameters) (radius : ℝ), 0 ≤ radius → radius ≤ 1 →
    ∀ cell : ℤ,
      (phaseWeight parameters radius cell ≤
          Real.exp (radialPhase parameters radius cell) ∧
        Real.exp (radialPhase parameters radius cell) ≤
          Real.exp (parameters.sigma0 + parameters.gamma) *
            phaseWeight parameters radius cell) ∧
      (cellFrequency cell ≤ cellPolynomialWeight cell ∧
        cellPolynomialWeight cell ≤ Real.sqrt 2 * cellFrequency cell)

end Grad.PhaseAlgebra
