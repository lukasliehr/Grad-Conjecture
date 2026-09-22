import RootUnitReal

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! The exact FA-nonlinear-root interface: the literal chart square root
`a(τ) = Σ_p c_p (τ·τ/2)^p` with the Q7 coefficients `c₀ = 1`,
`c_{p+1} = ((p - 1/2)/(p+1)) c_p`, its pointwise identification Q14 with the
positive square root `√(1 - |τ(ζ)|²/2)` on the literal Q13 ball
`‖τ‖_{T¹} < (2 C_ax)⁻¹`, and the one-high derivative bounds Q15 (including
the order-zero form) for a genuine iterated directional derivative tower in
every graded envelope. -/

variable {parameters : PhaseParameters}

/-- The literal chart square root `a(τ) = F(x(τ))`: the Q8 series at the
quadratic `x(τ) = τ·τ/2`, as realized by the accepted root-series engine. -/
def rootChart (family : TangentCoefficient parameters) : TameCoefficient parameters :=
  tameRootShifted 0 (tangentQuadratic family)

/-- FA-nonlinear-root. For every phase parameter set:
(a₀) on the literal Q13 ball, `a(τ)` is cellwise the literal Q8 series
`Σ_p c_p (τ·τ/2)^p` with the Q7 coefficients;
(a) for every real planar `τ` on the Q13 ball and every axial point `ζ`,
the pointwise argument satisfies `|τ(ζ)|²/2 < 1/8` and
`a(τ)(ζ) = √(1 - |τ(ζ)|²/2)`, the positive square root;
(b) there is a derivative tower starting at `a`, differentiating genuinely
in every graded envelope along the newest direction on the Q13 ball, whose
order-`j` level obeys the exact one-high estimate Q15
`|D^j a(τ)[h]|_s ≤ C_{s,j} [(1 + |τ|_s) Π_i |h_i|_0 + Σ_i |h_i|_s Π_{l≠i} |h_l|_0]`
with constants depending on `s, j` only. -/
def RootUnitGoal : Prop :=
  ∀ parameters : PhaseParameters,
    (∀ family : TangentCoefficient parameters, RootAxisCondition family → ∀ cell : ℤ,
      HasSum (fun p => ((rootCoefficient p : ℝ) : ℂ) * ((tangentQuadratic family) ^ p).val cell)
        ((rootChart family).val cell)) ∧
    (∀ family : TangentCoefficient parameters, RealTangent family → RootAxisCondition family →
      ∀ zeta : ℝ,
        ‖planarValue family zeta‖ ^ 2 / 2 < 1 / 8 ∧
        coefficientValue (rootChart family) zeta =
          ((Real.sqrt (1 - ‖planarValue family zeta‖ ^ 2 / 2) : ℝ) : ℂ)) ∧
    ∃ derivative : (order : ℕ) → TangentCoefficient parameters →
        (Fin order → TangentCoefficient parameters) → TameCoefficient parameters,
      (∀ family : TangentCoefficient parameters,
        derivative 0 family (fun position => position.elim0) = rootChart family) ∧
      (∀ (order : ℕ) (base : TangentCoefficient parameters)
        (directions : Fin (order + 1) → TangentCoefficient parameters),
        RootAxisCondition base →
        HasEnvDerivAt
          (fun t : ℝ => derivative order (base + (t : ℂ) • directions (Fin.last order))
            (fun position => directions position.castSucc))
          (derivative (order + 1) base directions)) ∧
      ∀ (grade order : ℕ), ∃ constant : ℝ, 0 ≤ constant ∧
        ∀ (base : TangentCoefficient parameters)
          (directions : Fin order → TangentCoefficient parameters),
          RootAxisCondition base →
          coefficientEnvelope grade (derivative order base directions) ≤
            constant * ((1 + tangentPlanarEnvelope grade base) *
                ∏ position, tangentPlanarEnvelope 0 (directions position) +
              ∑ position, tangentPlanarEnvelope grade (directions position) *
                ∏ other ∈ Finset.univ.erase position,
                  tangentPlanarEnvelope 0 (directions other))

end Grad.NonlinearQuotientBounds
