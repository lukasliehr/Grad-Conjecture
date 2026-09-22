import SeedQuantitative

noncomputable section

namespace Grad.Constraints.Seed

open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity Grad.GaugeCoefficients.Physical.Frame

/-- Private packaging of an already bounded bilinear operation. -/
def boundedLeftAction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (action : E → E → E)
    (addLeft : ∀ a b c, action (a + b) c = action a c + action b c)
    (smulLeft : ∀ (scalar : ℂ) a b, action (scalar • a) b = scalar • action a b)
    (addRight : ∀ a b c, action a (b + c) = action a b + action a c)
    (smulRight : ∀ (scalar : ℂ) a b, action a (scalar • b) = scalar • action a b)
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bound : ∀ a b, ‖action a b‖ ≤ constant * ‖a‖ * ‖b‖) : E →L[ℂ] (E →L[ℂ] E) := by
  let inner (a : E) : E →L[ℂ] E :=
    (show E →ₗ[ℂ] E from
      { toFun := action a
        map_add' := addRight a
        map_smul' := fun scalar b => smulRight scalar a b }).mkContinuous
      (constant * ‖a‖) (bound a)
  let outer : E →ₗ[ℂ] (E →L[ℂ] E) :=
    { toFun := inner
      map_add' := fun a b => ContinuousLinearMap.ext (fun c => addLeft a b c)
      map_smul' := fun scalar a => ContinuousLinearMap.ext (fun b => smulLeft scalar a b) }
  exact outer.mkContinuous constant (fun a => (inner a).opNorm_le_bound
    (mul_nonneg nonnegative (norm_nonneg a)) (bound a))

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) (grade dimension : ℕ)

def leftCompositionOperator :=
  boundedLeftAction (coefficientComposition admissible grade (inputDimension := dimension)
      (middleDimension := dimension) (outputDimension := dimension))
    (fun first second inner => by
      apply Subtype.ext
      exact rawComposition_add_outer admissible grade first.val second.val inner.val)
    (fun scalar outer inner => by
      apply Subtype.ext
      exact rawComposition_smul_outer admissible grade scalar outer.val inner.val)
    (fun outer first second => by
      apply Subtype.ext
      exact rawComposition_add_inner admissible grade outer.val first.val second.val)
    (fun scalar outer inner => by
      apply Subtype.ext
      exact rawComposition_smul_inner admissible grade scalar outer.val inner.val)
    (gradeProductConstant grade) (seedProductConstant_nonnegative grade)
    (coefficientComposition_norm_le admissible grade)

theorem leftCompositionOperator_apply
    (outer inner : Coefficient L sigma gamma ell grade dimension dimension) :
    leftCompositionOperator admissible grade dimension outer inner = coefficientComposition admissible grade outer inner := rfl

theorem leftCompositionOperator_power
    (outer : Coefficient L sigma gamma ell grade dimension dimension) (power : ℕ) :
    (leftCompositionOperator admissible grade dimension outer ^ power)
      (gradedIdentityCoefficient L sigma gamma ell grade dimension) = gradedCoefficientPower admissible outer power := by
  induction power with
  | zero => rfl
  | succ power inductionHypothesis =>
    rw [pow_succ']
    change leftCompositionOperator admissible grade dimension outer
      ((leftCompositionOperator admissible grade dimension outer ^ power)
        (gradedIdentityCoefficient L sigma gamma ell grade dimension)) = _
    exact congrArg (coefficientComposition admissible grade outer) inductionHypothesis

end Grad.Constraints.Seed
