import AJA21PositiveOrderedBounds
import AJA15GenericInverseSmooth
import AJB23ActualAxisDerivativeRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.AnnularKernelOrbit Grad.AnnularHighInverseOrbit Grad.AnnularInverseCalculus
open Grad.AnnularOrbitGenerators

section CurveLift
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

private theorem curveLift_hasFDerivAt (function : ℝ → A) (value : A) (point : OrbitParameter)
    (derivative : HasDerivAt function value point.1) :
    HasFDerivAt (fun tau : OrbitParameter => function tau.1) (orbitColumns value 0) point := by
  have actual := derivative.hasFDerivAt.comp point (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  apply actual.congr_fderiv
  apply ContinuousLinearMap.ext
  intro step
  change step.1 • value = step.1 • value + step.2 • (0 : A)
  simp only [smul_zero, add_zero]

/-- A one-variable jet is embedded with a constant second coordinate only to
reuse the accepted inverse-expression norm estimate. -/
def curveJet (function : ℝ → A) (angular cell : ℕ) (point : OrbitParameter) : A :=
  if cell = 0 then iteratedDeriv angular function point.1 else 0

private theorem curveJet_hasFDerivAt (function : ℝ → A) (smooth : ContDiff ℝ ∞ function)
    (angular cell : ℕ) (point : OrbitParameter) :
    HasFDerivAt (curveJet function angular cell)
      (orbitColumns (curveJet function (angular + 1) cell point)
        (curveJet function angular (cell + 1) point)) point := by
  by_cases zero : cell = 0
  · subst cell
    change HasFDerivAt (fun tau : OrbitParameter => iteratedDeriv angular function tau.1)
      (orbitColumns (iteratedDeriv (angular + 1) function point.1) 0) point
    rw [iteratedDeriv_succ]
    exact curveLift_hasFDerivAt (iteratedDeriv angular function) _ point
      (((smooth.differentiable_iteratedDeriv angular
        (by exact_mod_cast (show (angular : ℕ∞) < ⊤ from WithTop.coe_lt_top angular))) point.1).hasDerivAt)
  · have next : cell + 1 ≠ 0 := by omega
    have same : curveJet function angular cell = fun _ => 0 := by
      funext tau
      exact if_neg zero
    rw [same]
    simp only [curveJet, if_neg zero, if_neg next]
    have columns : orbitColumns (0 : A) 0 = 0 := by
      apply ContinuousLinearMap.ext
      intro step
      change step.1 • (0 : A) + step.2 • (0 : A) = 0
      simp only [smul_zero, add_zero]
    rw [columns]
    exact hasFDerivAt_const (0 : A) point

end CurveLift

section Inverse
variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]
  [CompleteSpace E]

private theorem curveInverse_columns (forward : ℝ → E →L[𝕜] F) (inverse : ℝ → F →L[𝕜] E)
    (smooth : ContDiff ℝ ∞ forward)
    (right : ∀ time, (forward time).comp (inverse time) = ContinuousLinearMap.id 𝕜 F)
    (left : ∀ time, (inverse time).comp (forward time) = ContinuousLinearMap.id 𝕜 E)
    (point : OrbitParameter) :
    HasFDerivAt (fun tau : OrbitParameter => inverse tau.1)
      (orbitColumns (-((inverse point.1).comp ((curveJet forward 1 0 point).comp (inverse point.1))))
        (-((inverse point.1).comp ((curveJet forward 0 1 point).comp (inverse point.1))))) point := by
  have derivative := curveJet_hasFDerivAt forward smooth 0 0 point
  simp only [curveJet, iteratedDeriv_zero] at derivative
  have actual := sameInverse_hasFDerivAt
    (fun tau : OrbitParameter => forward tau.1) (fun tau : OrbitParameter => inverse tau.1)
    (fun tau => right tau.1) (fun tau => left tau.1) point _ derivative
  apply actual.congr_fderiv
  exact orbitColumns_comp (E := E →L[𝕜] F) (F := F →L[𝕜] E)
    (inverseSandwich (inverse point.1)) _ _

/-- The genuine repeated one-variable derivative of the SAME inverse is the
already checked inverse word, evaluated using only that one-variable forward jet. -/
theorem iteratedDeriv_sameInverse_formula (forward : ℝ → E →L[𝕜] F) (inverse : ℝ → F →L[𝕜] E)
    (smooth : ContDiff ℝ ∞ forward)
    (right : ∀ time, (forward time).comp (inverse time) = ContinuousLinearMap.id 𝕜 F)
    (left : ∀ time, (inverse time).comp (forward time) = ContinuousLinearMap.id 𝕜 E)
    (order : ℕ) (time : ℝ) :
    iteratedDeriv order inverse time = (inverseDerivativeWord (List.replicate order false)).eval
      (fun tau => inverse tau.1) (curveJet forward) (time, 0) := by
  have inverseSmooth := sameInverse_contDiff forward inverse right left smooth
  have liftedSmooth : ContDiff ℝ ∞ (fun tau : OrbitParameter => inverse tau.1) :=
    inverseSmooth.comp contDiff_fst
  have restriction := iteratedDeriv_axis_restriction (fun tau : OrbitParameter => inverse tau.1)
    liftedSmooth false 0 order time
  have formula := orderedOrbitDerivative_inverse (fun tau : OrbitParameter => inverse tau.1) (curveJet forward)
    (curveInverse_columns forward inverse smooth right left) (curveJet_hasFDerivAt forward smooth)
    (List.replicate order false) (time, 0)
  simp only [axisVector, Bool.false_eq_true, if_false, Prod.smul_mk, smul_eq_mul,
    mul_one, mul_zero, zero_add] at restriction
  exact restriction.trans formula

/-- One-high control for a genuine pure-coordinate derivative of an inverse;
all constants are separate from the budget and the evaluation point. -/
theorem iteratedDeriv_sameInverse_oneHigh (forward : ℝ → E →L[𝕜] F) (inverse : ℝ → F →L[𝕜] E)
    (smooth : ContDiff ℝ ∞ forward)
    (right : ∀ time, (forward time).comp (inverse time) = ContinuousLinearMap.id 𝕜 F)
    (left : ∀ time, (inverse time).comp (forward time) = ContinuousLinearMap.id 𝕜 E)
    (budget : ℕ → ℝ) (budgetNonnegative : ∀ n, 0 ≤ budget n) (budgetMonotone : Monotone budget)
    (inverseBound : ℝ) (jetBound pairBound : ℕ → ℝ)
    (inverseNonnegative : 0 ≤ inverseBound) (jetNonnegative : ∀ n, 0 ≤ jetBound n)
    (pairNonnegative : ∀ n, 0 ≤ pairBound n)
    (inverseEstimate : ∀ time, ‖inverse time‖ ≤ inverseBound)
    (jetEstimate : ∀ order, 0 < order → ∀ time, ‖iteratedDeriv order forward time‖ ≤ jetBound order * budget order)
    (pairEstimate : ∀ a b, budget a * budget b ≤ pairBound (a + b) * budget (a + b))
    (order : ℕ) (positive : 0 < order) (time : ℝ) :
    ‖iteratedDeriv order inverse time‖ ≤
      (inverseDerivativeWord (List.replicate order false)).bound inverseBound (fun a c => jetBound (a + c)) pairBound * budget order := by
  rw [iteratedDeriv_sameInverse_formula forward inverse smooth right left]
  have nonempty : List.replicate order false ≠ [] := by simp only [ne_eq, List.replicate_eq_nil_iff]; omega
  have estimate := (inverseDerivativeWord (List.replicate order false)).norm_eval_le_positive
    (fun tau => inverse tau.1) (curveJet forward) (time, 0) budget budgetNonnegative budgetMonotone
    inverseBound (fun a c => jetBound (a + c)) pairBound inverseNonnegative (fun a c => jetNonnegative (a + c)) pairNonnegative
    (inverseEstimate time) (fun angular cell orderPositive => by
      by_cases zero : cell = 0
      · subst cell
        simpa only [curveJet, ↓reduceIte, Nat.add_zero] using jetEstimate angular (by omega) time
      · simp only [curveJet, if_neg zero, norm_zero]
        exact mul_nonneg (jetNonnegative _) (budgetNonnegative _))
    pairEstimate (inverseDerivativeWord_positive nonempty)
  exact estimate.trans (mul_le_mul_of_nonneg_left
    (budgetMonotone (by simpa only [List.length_replicate] using inverseDerivativeWord_degree (List.replicate order false)))
    ((inverseDerivativeWord (List.replicate order false)).bound_nonnegative inverseBound _ pairBound
      inverseNonnegative (fun a c => jetNonnegative (a + c)) pairNonnegative))
end Inverse
end Grad.AnnularCrossOrbit
