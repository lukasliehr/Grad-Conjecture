import AJA18OrderedInverseWords

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.AnnularInverseCalculus
open Grad.AnnularKernelOrbit Grad.AnnularHighInverseOrbit

def axisVector (axis : Bool) : OrbitParameter := if axis then (0, 1) else (1, 0)

noncomputable def orderedOrbitDerivative {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] :
    List Bool → (OrbitParameter → A) → OrbitParameter → A
  | [], function => function
  | axis :: tail, function => fun point => fderiv ℝ (orderedOrbitDerivative tail function) point (axisVector axis)

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

namespace InverseExpression

theorem axisDerivative_eval (inverse : OrbitParameter → F →L[𝕜] E)
    (jet : ℕ → ℕ → OrbitParameter → E →L[𝕜] F)
    (inverseDerivative : ∀ point, HasFDerivAt inverse
      (orbitColumns (-((inverse point).comp ((jet 1 0 point).comp (inverse point))))
        (-((inverse point).comp ((jet 0 1 point).comp (inverse point))))) point)
    (jetDerivative : ∀ angular cell point, HasFDerivAt (jet angular cell)
      (orbitColumns (jet (angular + 1) cell point) (jet angular (cell + 1) point)) point)
    (expression : InverseExpression) (axis : Bool) (point : OrbitParameter) :
    fderiv ℝ (fun tau => expression.eval inverse jet tau) point (axisVector axis) =
      (expression.derivative axis).eval inverse jet point := by
  rw [(expression.hasFDerivAt inverse jet inverseDerivative jetDerivative point).fderiv]
  cases axis <;> simp only [axisVector, Bool.false_eq_true, ↓reduceIte, orbitColumns_apply, zero_smul, one_smul, zero_add, add_zero]

noncomputable def bound (inverseBound : ℝ) (jetBound : ℕ → ℕ → ℝ) (pairBound : ℕ → ℝ) : InverseExpression → ℝ
  | .inverse => inverseBound
  | .add first second => first.bound inverseBound jetBound pairBound + second.bound inverseBound jetBound pairBound
  | .neg expression => expression.bound inverseBound jetBound pairBound
  | .chain angular cell _ tail => inverseBound * jetBound angular cell * tail.bound inverseBound jetBound pairBound *
      (1 + pairBound (angular + cell + tail.degree))

theorem bound_nonnegative (inverseBound : ℝ) (jetBound : ℕ → ℕ → ℝ) (pairBound : ℕ → ℝ)
    (inverseNonnegative : 0 ≤ inverseBound) (jetNonnegative : ∀ a c, 0 ≤ jetBound a c)
    (pairNonnegative : ∀ n, 0 ≤ pairBound n) (expression : InverseExpression) :
    0 ≤ expression.bound inverseBound jetBound pairBound := by
  induction expression with
  | inverse => exact inverseNonnegative
  | add first second ihFirst ihSecond => exact add_nonneg ihFirst ihSecond
  | neg expression ih => exact ih
  | chain angular cell positive tail ih =>
    exact mul_nonneg (mul_nonneg (mul_nonneg inverseNonnegative (jetNonnegative angular cell)) ih)
      (add_nonneg zero_le_one (pairNonnegative _))

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] in
theorem norm_eval_le (inverse : OrbitParameter → F →L[𝕜] E)
    (jet : ℕ → ℕ → OrbitParameter → E →L[𝕜] F) (point : OrbitParameter)
    (budget : ℕ → ℝ) (budgetNonnegative : ∀ n, 0 ≤ budget n) (budgetMonotone : Monotone budget)
    (inverseBound : ℝ) (jetBound : ℕ → ℕ → ℝ) (pairBound : ℕ → ℝ)
    (inverseNonnegative : 0 ≤ inverseBound) (jetNonnegative : ∀ a c, 0 ≤ jetBound a c)
    (pairNonnegative : ∀ n, 0 ≤ pairBound n)
    (inverseEstimate : ‖inverse point‖ ≤ inverseBound)
    (jetEstimate : ∀ a c, 0 < a + c → ‖jet a c point‖ ≤ jetBound a c * budget (a + c))
    (pairEstimate : ∀ a b, budget a * budget b ≤ pairBound (a + b) * budget (a + b))
    (expression : InverseExpression) :
    ‖expression.eval inverse jet point‖ ≤ expression.bound inverseBound jetBound pairBound * (1 + budget expression.degree) := by
  induction expression with
  | inverse =>
    change ‖inverse point‖ ≤ inverseBound * (1 + budget 0)
    exact inverseEstimate.trans (le_mul_of_one_le_right inverseNonnegative (by have := budgetNonnegative 0; linarith))
  | add first second ihFirst ihSecond =>
    have firstBound : first.bound inverseBound jetBound pairBound * (1 + budget first.degree) ≤
        first.bound inverseBound jetBound pairBound * (1 + budget (max first.degree second.degree)) :=
      mul_le_mul_of_nonneg_left (by linarith only [budgetMonotone (Nat.le_max_left first.degree second.degree)])
        (first.bound_nonnegative inverseBound jetBound pairBound inverseNonnegative jetNonnegative pairNonnegative)
    have secondBound : second.bound inverseBound jetBound pairBound * (1 + budget second.degree) ≤
        second.bound inverseBound jetBound pairBound * (1 + budget (max first.degree second.degree)) :=
      mul_le_mul_of_nonneg_left (by linarith only [budgetMonotone (Nat.le_max_right first.degree second.degree)])
        (second.bound_nonnegative inverseBound jetBound pairBound inverseNonnegative jetNonnegative pairNonnegative)
    have firstEstimate := ihFirst
    have secondEstimate := ihSecond
    have sumNorm := norm_add_le (first.eval inverse jet point) (second.eval inverse jet point)
    change ‖first.eval inverse jet point + second.eval inverse jet point‖ ≤
      (first.bound inverseBound jetBound pairBound + second.bound inverseBound jetBound pairBound) * (1 + budget (max first.degree second.degree))
    nlinarith only [sumNorm, firstEstimate, secondEstimate, firstBound, secondBound]
  | neg expression ih => simpa only [eval, norm_neg, bound, degree] using ih
  | chain angular cell positive tail ih =>
    have tailNonnegative := tail.bound_nonnegative inverseBound jetBound pairBound inverseNonnegative jetNonnegative pairNonnegative
    have coefficientNonnegative := jetNonnegative angular cell
    have highNonnegative := budgetNonnegative (angular + cell + tail.degree)
    have lowHigh := budgetMonotone (show angular + cell ≤ angular + cell + tail.degree by omega)
    have pair := pairEstimate (angular + cell) tail.degree
    have budgetProduct : budget (angular + cell) * (1 + budget tail.degree) ≤
        (1 + pairBound (angular + cell + tail.degree)) * (1 + budget (angular + cell + tail.degree)) := by
      have pairC := pairNonnegative (angular + cell + tail.degree)
      nlinarith
    have first := ContinuousLinearMap.opNorm_comp_le (inverse point) ((jet angular cell point).comp (tail.eval inverse jet point))
    have second := ContinuousLinearMap.opNorm_comp_le (jet angular cell point) (tail.eval inverse jet point)
    have inner := (mul_le_mul (jetEstimate angular cell positive) ih (norm_nonneg _)
      (mul_nonneg coefficientNonnegative (budgetNonnegative _)))
    have whole := first.trans ((mul_le_mul inverseEstimate (second.trans inner) (norm_nonneg _)
      inverseNonnegative))
    have scaled := mul_le_mul_of_nonneg_left budgetProduct
      (mul_nonneg (mul_nonneg inverseNonnegative coefficientNonnegative) tailNonnegative)
    apply whole.trans
    change inverseBound * (jetBound angular cell * budget (angular + cell) *
      (tail.bound inverseBound jetBound pairBound * (1 + budget tail.degree))) ≤
      (inverseBound * jetBound angular cell * tail.bound inverseBound jetBound pairBound *
        (1 + pairBound (angular + cell + tail.degree))) * (1 + budget (angular + cell + tail.degree))
    nlinarith only [scaled]


end InverseExpression

theorem orderedOrbitDerivative_inverse (inverse : OrbitParameter → F →L[𝕜] E)
    (jet : ℕ → ℕ → OrbitParameter → E →L[𝕜] F)
    (inverseDerivative : ∀ point, HasFDerivAt inverse
      (orbitColumns (-((inverse point).comp ((jet 1 0 point).comp (inverse point))))
        (-((inverse point).comp ((jet 0 1 point).comp (inverse point))))) point)
    (jetDerivative : ∀ angular cell point, HasFDerivAt (jet angular cell)
      (orbitColumns (jet (angular + 1) cell point) (jet angular (cell + 1) point)) point)
    (word : List Bool) (point : OrbitParameter) :
    orderedOrbitDerivative word inverse point = (inverseDerivativeWord word).eval inverse jet point := by
  induction word generalizing point with
  | nil => rfl
  | cons axis tail ih =>
    have equality := funext ih
    change fderiv ℝ (orderedOrbitDerivative tail inverse) point (axisVector axis) = _
    rw [equality]
    exact (inverseDerivativeWord tail).axisDerivative_eval inverse jet inverseDerivative jetDerivative axis point

end Grad.AnnularInverseCalculus
