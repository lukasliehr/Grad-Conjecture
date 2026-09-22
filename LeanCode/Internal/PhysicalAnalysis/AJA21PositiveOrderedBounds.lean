import AJA19OrderedInverseBounds

noncomputable section
set_option autoImplicit false
namespace Grad.AnnularInverseCalculus
open Grad.AnnularKernelOrbit
namespace InverseExpression

noncomputable def Positive : InverseExpression → Prop
  | .inverse => False
  | .add first second => first.Positive ∧ second.Positive
  | .neg expression => expression.Positive
  | .chain _ _ _ _ => True

theorem derivative_positive (expression : InverseExpression) (axis : Bool) :
    (expression.derivative axis).Positive := by
  induction expression <;> simp_all only [derivative, Positive, and_self]

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] in
theorem norm_eval_le_positive (inverse : OrbitParameter → F →L[𝕜] E)
    (jet : ℕ → ℕ → OrbitParameter → E →L[𝕜] F) (point : OrbitParameter)
    (budget : ℕ → ℝ) (budgetNonnegative : ∀ n, 0 ≤ budget n) (budgetMonotone : Monotone budget)
    (inverseBound : ℝ) (jetBound : ℕ → ℕ → ℝ) (pairBound : ℕ → ℝ)
    (inverseNonnegative : 0 ≤ inverseBound) (jetNonnegative : ∀ a c, 0 ≤ jetBound a c)
    (pairNonnegative : ∀ n, 0 ≤ pairBound n)
    (inverseEstimate : ‖inverse point‖ ≤ inverseBound)
    (jetEstimate : ∀ a c, 0 < a + c → ‖jet a c point‖ ≤ jetBound a c * budget (a + c))
    (pairEstimate : ∀ a b, budget a * budget b ≤ pairBound (a + b) * budget (a + b))
    (expression : InverseExpression) (hasJet : expression.Positive) :
    ‖expression.eval inverse jet point‖ ≤ expression.bound inverseBound jetBound pairBound * budget expression.degree := by
  induction expression with
  | inverse => exact hasJet.elim
  | add first second ihFirst ihSecond =>
    have firstBound : first.bound inverseBound jetBound pairBound * budget first.degree ≤
        first.bound inverseBound jetBound pairBound * budget (max first.degree second.degree) :=
      mul_le_mul_of_nonneg_left (by linarith only [budgetMonotone (Nat.le_max_left first.degree second.degree)])
        (first.bound_nonnegative inverseBound jetBound pairBound inverseNonnegative jetNonnegative pairNonnegative)
    have secondBound : second.bound inverseBound jetBound pairBound * budget second.degree ≤
        second.bound inverseBound jetBound pairBound * budget (max first.degree second.degree) :=
      mul_le_mul_of_nonneg_left (by linarith only [budgetMonotone (Nat.le_max_right first.degree second.degree)])
        (second.bound_nonnegative inverseBound jetBound pairBound inverseNonnegative jetNonnegative pairNonnegative)
    have firstEstimate := ihFirst hasJet.1
    have secondEstimate := ihSecond hasJet.2
    have sumNorm := norm_add_le (first.eval inverse jet point) (second.eval inverse jet point)
    change ‖first.eval inverse jet point + second.eval inverse jet point‖ ≤
      (first.bound inverseBound jetBound pairBound + second.bound inverseBound jetBound pairBound) * budget (max first.degree second.degree)
    nlinarith only [sumNorm, firstEstimate, secondEstimate, firstBound, secondBound]
  | neg expression ih => simpa only [eval, norm_neg, bound, degree] using ih hasJet
  | chain angular cell positive tail _ =>
    have tailEstimate := tail.norm_eval_le inverse jet point budget budgetNonnegative budgetMonotone
      inverseBound jetBound pairBound inverseNonnegative jetNonnegative pairNonnegative inverseEstimate jetEstimate pairEstimate
    have tailNonnegative := tail.bound_nonnegative inverseBound jetBound pairBound inverseNonnegative jetNonnegative pairNonnegative
    have coefficientNonnegative := jetNonnegative angular cell
    have lowHigh := budgetMonotone (show angular + cell ≤ angular + cell + tail.degree by omega)
    have pair := pairEstimate (angular + cell) tail.degree
    have budgetProduct : budget (angular + cell) * (1 + budget tail.degree) ≤
        (1 + pairBound (angular + cell + tail.degree)) * budget (angular + cell + tail.degree) := by
      nlinarith
    have first := ContinuousLinearMap.opNorm_comp_le (inverse point) ((jet angular cell point).comp (tail.eval inverse jet point))
    have second := ContinuousLinearMap.opNorm_comp_le (jet angular cell point) (tail.eval inverse jet point)
    have inner := mul_le_mul (jetEstimate angular cell positive) tailEstimate (norm_nonneg _)
      (mul_nonneg coefficientNonnegative (budgetNonnegative _))
    have whole := first.trans (mul_le_mul inverseEstimate (second.trans inner) (norm_nonneg _) inverseNonnegative)
    have scaled := mul_le_mul_of_nonneg_left budgetProduct
      (mul_nonneg (mul_nonneg inverseNonnegative coefficientNonnegative) tailNonnegative)
    apply whole.trans
    change inverseBound * (jetBound angular cell * budget (angular + cell) *
      (tail.bound inverseBound jetBound pairBound * (1 + budget tail.degree))) ≤
      (inverseBound * jetBound angular cell * tail.bound inverseBound jetBound pairBound *
        (1 + pairBound (angular + cell + tail.degree))) * budget (angular + cell + tail.degree)
    nlinarith only [scaled]


end InverseExpression

theorem inverseDerivativeWord_positive {word : List Bool} (nonempty : word ≠ []) :
    (inverseDerivativeWord word).Positive := by
  cases word with
  | nil => exact (nonempty rfl).elim
  | cons axis tail => exact (inverseDerivativeWord tail).derivative_positive axis

end Grad.AnnularInverseCalculus
