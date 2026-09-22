import TameRootSeries
import SeedExponentialSmooth

/-!
# NG_F06: coefficient-series majorants at a fixed grade — interface

Blueprint unit NG_F06 (group `finite_banach_calculus`, source atom
R5:Q8-N3-majorants): at one fixed output grade and derivative order `j`, the
operator derivative series majorants for the Q8 square-root coefficient
series (`|c_p| ≤ 1` on `|x|_0 ≤ θ' < 1`) and for the N3 seed exponential
coefficients (on bounded parameter balls) are summable on each specified
bounded high-grade ball.

## Q8 (accepted objects: `rootCoefficient`, `rootDerivativeCoefficient`,
`TameCoefficient`, `coefficientEnvelope` of the FA-nonlinear-tame root)

The series `F(x) = Σ_p c_p x^p` lives in the accepted commutative
coefficient algebra. The `j`-th derivative of the `p`-th summand along the
directions `h_1, …, h_j` is the algebra element
`c_p · p^{\underline j} · x^{p-j} · h_1 ⋯ h_j` (`rootDerivativeTerm`); with the
derivative-shifted coefficients this is `c^{(j)}_{p-j} · x^{p-j} · h_1 ⋯ h_j`
where `c^{(j)}_q = (q+j)^{\underline j} c_{q+j}` is the accepted
`rootDerivativeCoefficient j q`. On the ball `|x|_0 ≤ θ'`, `|x|_s ≤ R` the
accepted Q6 one-high placement estimates bound its grade-`s` envelope by the
explicit majorant `rootOperatorMajorant` times `∏_i |h_i|_s`: the majorant is
`|c_p| p^{\underline j}` times a fixed polynomial in `p` times `θ'^{p-j-1}`
(the high slot on `x`) or `θ'^{p-j}` (the high slot on a direction).

## N3 (accepted objects: `seedExponentialTerm`, `gradedCoefficientPower`,
`coefficientComposition`, `gradeProductConstant`, `gradedIdentityCoefficient`
of the gauge-coefficient roots, and `leftCompositionOperator` of the seed root)

The seed exponential `exp(A) = Σ_p A^p / p!` has `p`-th summand
`seedExponentialTerm A p = (p!)⁻¹ • A^p` with `A^p` the ordered composition
word `A ∘ ⋯ ∘ A` applied to the graded identity. The `j`-th derivative of the
`p`-th summand along directions `h_1, …, h_j` is `(p!)⁻¹` times the sum over
all `p^{\underline j}` placements of the `j` directions among the `p` slots
of the ordered composition word with the directions in the chosen slots and
`A` elsewhere (`exponentialDerivativeTerm`). On the ball `‖A‖ ≤ R` its norm
is bounded by the explicit factorial-denominator majorant
`expOperatorMajorant = ‖I‖ · (p^{\underline j} / p!) · K^p · R^{p-j}` times
`∏_i ‖h_i‖`, where `K = gradeProductConstant grade` is the accepted
composition constant.
-/

noncomputable section

open scoped BigOperators

namespace Grad.CoefficientMajorants

open Grad.NonlinearQuotientBounds Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity Grad.GaugeCoefficients.Physical.Frame
open Grad.Constraints.Seed

/-! ### Q8: the square-root coefficient series -/

section Root

variable {parameters : PhaseParameters}

/-- The `order`-th derivative of the `p`-th root-series summand `c_p x^p` along
the directions `h_1, …, h_order` in the commutative coefficient algebra:
`c_p · p^{\underline{order}} · x^{p-order} · h_1 ⋯ h_order`. -/
def rootDerivativeTerm (order p : ℕ) (x : TameCoefficient parameters)
    (directions : Fin order → TameCoefficient parameters) : TameCoefficient parameters :=
  ((rootCoefficient p * (p.descFactorial order : ℝ) : ℝ) : ℂ) •
    (x ^ (p - order) * ∏ index, directions index)

/-- The Q8 operator derivative series majorant at output grade `grade`,
derivative order `order`, low radius `theta` and high radius `radius`. -/
def rootOperatorMajorant (parameters : PhaseParameters) (grade order : ℕ)
    (theta radius : ℝ) (p : ℕ) : ℝ :=
  |rootCoefficient p| * (p.descFactorial order : ℝ) *
    ((2 : ℝ) ^ grade * Real.exp parameters.sigma0 ^ 2 *
      (((p - order + 1 : ℕ) : ℝ) ^ (grade + 1) * (radius + 1) * theta ^ (p - order - 1) +
        ((order + 1 : ℕ) : ℝ) ^ (grade + 1) * theta ^ (p - order)))

end Root

/-! ### N3: the seed exponential coefficients -/

section Exponential

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}

/-- The ordered composition word `f_0 ∘ f_1 ∘ ⋯ ∘ f_{p-1}` applied to the graded
identity, in the written composition order of the accepted powers. -/
noncomputable def compositionWord :
    (p : ℕ) → (Fin p → Coefficient L sigma gamma ell grade dimension dimension) →
      Coefficient L sigma gamma ell grade dimension dimension
  | 0, _ => gradedIdentityCoefficient L sigma gamma ell grade dimension
  | p + 1, factors =>
      coefficientComposition admissible grade (factors 0)
        (compositionWord p (Fin.tail factors))

/-- The factors of one placement: the direction `h_i` in slot `placement i`,
the base element in every other slot. -/
def placedFactor {order p : ℕ} (placement : Fin order ↪ Fin p)
    (base : Coefficient L sigma gamma ell grade dimension dimension)
    (directions : Fin order → Coefficient L sigma gamma ell grade dimension dimension)
    (slot : Fin p) : Coefficient L sigma gamma ell grade dimension dimension :=
  if hit : ∃ index, placement index = slot then directions (Classical.choose hit) else base

/-- The `order`-th derivative of the `p`-th exponential summand `A^p / p!` along
the directions `h_1, …, h_order`: `(p!)⁻¹` times the sum over all placements of
the directions among the `p` slots of the ordered composition word. -/
def exponentialDerivativeTerm (order p : ℕ)
    (base : Coefficient L sigma gamma ell grade dimension dimension)
    (directions : Fin order → Coefficient L sigma gamma ell grade dimension dimension) :
    Coefficient L sigma gamma ell grade dimension dimension :=
  ((p.factorial : ℂ)⁻¹) •
    ∑ placement : Fin order ↪ Fin p,
      compositionWord admissible p (placedFactor placement base directions)

end Exponential

/-- The N3 operator derivative series majorant at grade `grade`, derivative
order `order`, identity norm `identityNorm` and generator radius `radius`:
`‖I‖ · (p^{\underline{order}} / p!) · K^p · R^{p-order}`. -/
def expOperatorMajorant (grade : ℕ) (identityNorm radius : ℝ) (order p : ℕ) : ℝ :=
  identityNorm * ((p.descFactorial order : ℝ) / (p.factorial : ℝ)) *
    gradeProductConstant grade ^ p * radius ^ (p - order)


/-- NG_F06. (Q8) For every phase parameter set, output grade, derivative order
and ball `|x|_0 ≤ θ' < 1`, `|x|_s ≤ R`: the explicit majorant
`rootOperatorMajorant` is summable, and it dominates the grade-`s` envelope of
every derivative term `c_p p^{\underline j} x^{p-j} h_1 ⋯ h_j` uniformly on the
ball, linearly in `∏_i |h_i|_s`. (N3) For every admissible width, grade,
dimension, derivative order and radius `R`: the explicit factorial-denominator
majorant `expOperatorMajorant` is summable; the order-zero derivative terms
are exactly the accepted exponential summands `seedExponentialTerm`; and the
majorant dominates the norm of every derivative term uniformly on the ball
`‖A‖ ≤ R`, linearly in `∏_i ‖h_i‖`. -/
def CoefficientMajorantGoal : Prop :=
  (∀ (parameters : PhaseParameters) (grade order : ℕ) (theta radius : ℝ),
      0 ≤ theta → theta < 1 → 0 ≤ radius →
      Summable (rootOperatorMajorant parameters grade order theta radius) ∧
      ∀ x : TameCoefficient parameters, coefficientEnvelope 0 x ≤ theta →
        coefficientEnvelope grade x ≤ radius →
        ∀ (directions : Fin order → TameCoefficient parameters) (p : ℕ),
          coefficientEnvelope grade (rootDerivativeTerm order p x directions) ≤
            rootOperatorMajorant parameters grade order theta radius p *
              ∏ index, coefficientEnvelope grade (directions index)) ∧
  (∀ {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
      (grade dimension order : ℕ) (radius : ℝ), 0 ≤ radius →
      Summable (expOperatorMajorant grade
        ‖gradedIdentityCoefficient L sigma gamma ell grade dimension‖ radius order) ∧
      (∀ (base : Coefficient L sigma gamma ell grade dimension dimension) (p : ℕ),
        exponentialDerivativeTerm admissible 0 p base
            (fun index => index.elim0) =
          seedExponentialTerm admissible base p) ∧
      ∀ base : Coefficient L sigma gamma ell grade dimension dimension, ‖base‖ ≤ radius →
        ∀ (directions : Fin order → Coefficient L sigma gamma ell grade dimension dimension)
          (p : ℕ),
          ‖exponentialDerivativeTerm admissible order p base directions‖ ≤
            expOperatorMajorant grade
                ‖gradedIdentityCoefficient L sigma gamma ell grade dimension‖ radius order p *
              ∏ index, ‖directions index‖)

end Grad.CoefficientMajorants
