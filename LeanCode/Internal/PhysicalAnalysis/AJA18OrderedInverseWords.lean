import AJA13RealOrbitColumns
import AJA11GenericInverseDerivative
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

noncomputable section
set_option autoImplicit false
namespace Grad.AnnularInverseCalculus
open Grad.AnnularKernelOrbit Grad.AnnularHighInverseOrbit

section Bilinear
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem bilinearColumns_hasFDerivAt (product : E →L[ℝ] F →L[ℝ] G)
    (first : OrbitParameter → E) (second : OrbitParameter → F) (a b : E) (c d : F)
    (point : OrbitParameter) (hf : HasFDerivAt first (orbitColumns a b) point)
    (hg : HasFDerivAt second (orbitColumns c d) point) :
    HasFDerivAt (fun tau => product (first tau) (second tau))
      (orbitColumns (product a (second point) + product (first point) c)
        (product b (second point) + product (first point) d)) point := by
  have derivative := product.hasFDerivAt_of_bilinear hf hg
  apply derivative.congr_fderiv
  apply ContinuousLinearMap.ext
  intro step
  change product (first point) (step.1 • c + step.2 • d) +
    product (step.1 • a + step.2 • b) (second point) =
    step.1 • (product a (second point) + product (first point) c) +
      step.2 • (product b (second point) + product (first point) d)
  simp only [map_add, map_smul, add_apply, smul_apply, smul_add]
  abel
end Bilinear

inductive InverseExpression where
  | inverse
  | add (first second : InverseExpression)
  | neg (expression : InverseExpression)
  | chain (angular cell : ℕ) (positive : 0 < angular + cell) (tail : InverseExpression)

namespace InverseExpression

noncomputable def degree : InverseExpression → ℕ
  | .inverse => 0
  | .add first second => max first.degree second.degree
  | .neg expression => expression.degree
  | .chain angular cell _ tail => angular + cell + tail.degree

noncomputable def derivative (axis : Bool) : InverseExpression → InverseExpression
  | .inverse => .neg (.chain (if axis then 0 else 1) (if axis then 1 else 0) (by cases axis <;> simp) .inverse)
  | .add first second => .add (first.derivative axis) (second.derivative axis)
  | .neg expression => .neg (expression.derivative axis)
  | .chain angular cell positive tail =>
    .add (.neg (.chain (if axis then 0 else 1) (if axis then 1 else 0) (by cases axis <;> simp)
      (.chain angular cell positive tail)))
      (.add (.chain (angular + if axis then 0 else 1) (cell + if axis then 1 else 0)
        (by cases axis <;> simp_all) tail)
        (.chain angular cell positive (tail.derivative axis)))

theorem derivative_degree (expression : InverseExpression) (axis : Bool) :
    (expression.derivative axis).degree ≤ expression.degree + 1 := by
  induction expression with
  | inverse => cases axis <;> simp [derivative, degree]
  | add first second ihFirst ihSecond => simp only [derivative, degree]; omega
  | neg expression ih => exact ih
  | chain angular cell positive tail ih => cases axis <;> simp_all only [derivative, degree, Bool.false_eq_true,
      ↓reduceIte, Nat.zero_add, Nat.add_zero] <;> omega

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

noncomputable def eval (inverse : OrbitParameter → F →L[𝕜] E)
    (jet : ℕ → ℕ → OrbitParameter → E →L[𝕜] F) (point : OrbitParameter) : InverseExpression → F →L[𝕜] E
  | .inverse => inverse point
  | .add first second => first.eval inverse jet point + second.eval inverse jet point
  | .neg expression => -expression.eval inverse jet point
  | .chain angular cell _ tail => (inverse point).comp ((jet angular cell point).comp (tail.eval inverse jet point))

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] in
private theorem chainRuleValue (inverse : F →L[𝕜] E) (dInverse : E →L[𝕜] F)
    (coefficient dCoefficient : E →L[𝕜] F) (tail dTail : F →L[𝕜] E) :
    (-inverse.comp (dInverse.comp inverse)).comp (coefficient.comp tail) +
      inverse.comp (dCoefficient.comp tail + coefficient.comp dTail) =
    -(inverse.comp (dInverse.comp (inverse.comp (coefficient.comp tail)))) +
      (inverse.comp (dCoefficient.comp tail) + inverse.comp (coefficient.comp dTail)) := by
  apply ContinuousLinearMap.ext
  intro source
  change -(inverse (dInverse (inverse (coefficient (tail source))))) +
    inverse (dCoefficient (tail source) + coefficient (dTail source)) = _
  rw [map_add]
  rfl

theorem hasFDerivAt (inverse : OrbitParameter → F →L[𝕜] E)
    (jet : ℕ → ℕ → OrbitParameter → E →L[𝕜] F)
    (inverseDerivative : ∀ point, HasFDerivAt inverse
      (orbitColumns (-((inverse point).comp ((jet 1 0 point).comp (inverse point))))
        (-((inverse point).comp ((jet 0 1 point).comp (inverse point))))) point)
    (jetDerivative : ∀ angular cell point, HasFDerivAt (jet angular cell)
      (orbitColumns (jet (angular + 1) cell point) (jet angular (cell + 1) point)) point)
    (expression : InverseExpression) (point : OrbitParameter) :
    HasFDerivAt (fun tau => expression.eval inverse jet tau)
      (orbitColumns ((expression.derivative false).eval inverse jet point)
        ((expression.derivative true).eval inverse jet point)) point := by
  induction expression with
  | inverse => exact inverseDerivative point
  | add first second ihFirst ihSecond => exact sumOrbit_hasFDerivAt _ _ _ _ _ _ point ihFirst ihSecond
  | neg expression ih =>
    apply ih.neg.congr_fderiv
    apply ContinuousLinearMap.ext
    intro step
    change -(step.1 • (expression.derivative false).eval inverse jet point +
      step.2 • (expression.derivative true).eval inverse jet point) =
      step.1 • (-(expression.derivative false).eval inverse jet point) +
        step.2 • (-(expression.derivative true).eval inverse jet point)
    simp only [smul_neg, neg_add]
  | chain angular cell positive tail ih =>
    have inner := bilinearColumns_hasFDerivAt
      ((ContinuousLinearMap.compL 𝕜 F E F).bilinearRestrictScalars ℝ)
      (jet angular cell) (fun tau => tail.eval inverse jet tau) _ _ _ _ point
      (jetDerivative angular cell point) ih
    have outer := bilinearColumns_hasFDerivAt
      ((ContinuousLinearMap.compL 𝕜 F F E).bilinearRestrictScalars ℝ)
      inverse (fun tau => (jet angular cell tau).comp (tail.eval inverse jet tau)) _ _ _ _ point
      (inverseDerivative point) inner
    apply outer.congr_fderiv
    apply congrArg₂ orbitColumns
    · exact chainRuleValue (inverse point) (jet 1 0 point) (jet angular cell point)
        (jet (angular + 1) cell point) (tail.eval inverse jet point)
        ((tail.derivative false).eval inverse jet point)
    · exact chainRuleValue (inverse point) (jet 0 1 point) (jet angular cell point)
        (jet angular (cell + 1) point) (tail.eval inverse jet point)
        ((tail.derivative true).eval inverse jet point)

end InverseExpression

noncomputable def inverseDerivativeWord : List Bool → InverseExpression
  | [] => .inverse
  | axis :: tail => (inverseDerivativeWord tail).derivative axis

theorem inverseDerivativeWord_degree (word : List Bool) : (inverseDerivativeWord word).degree ≤ word.length := by
  induction word with
  | nil => rfl
  | cons axis tail ih => exact ((inverseDerivativeWord tail).derivative_degree axis).trans (by simpa using Nat.add_le_add_right ih 1)

end Grad.AnnularInverseCalculus
