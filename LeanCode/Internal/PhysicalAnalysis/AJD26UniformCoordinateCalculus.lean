import AJD25PureCoordinateProductEstimates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped ContDiff BigOperators
namespace Grad.AnnularCrossOrbit
open Grad.AnnularKernelOrbit Grad.AnnularInverseCalculus Grad.AnnularOrbitGenerators

variable {Context : Type*} {E F G : Context → Type*}
  [∀ context, NormedAddCommGroup (E context)] [∀ context, NormedSpace ℝ (E context)]
  [∀ context, NormedAddCommGroup (F context)] [∀ context, NormedSpace ℝ (F context)]
  [∀ context, NormedAddCommGroup (G context)] [∀ context, NormedSpace ℝ (G context)]

/-- The quantifiers enforce one constant before the physical context,
base translation, or evaluation time. Positive orders carry one high factor. -/
def UniformCoordinateBound (budget : Context → ℕ → ℝ)
    (family : (context : Context) → OrbitParameter → E context) : Prop :=
  ∀ axis order, ∃ constant : ℝ, 0 ≤ constant ∧ ∀ context base time,
    ‖iteratedDeriv order (fun t : ℝ => family context (base + t • axisVector axis)) time‖ ≤
      constant * coordinateJetWeight (budget context) order

namespace UniformCoordinateBound
variable {budget : Context → ℕ → ℝ}
  {first : (context : Context) → OrbitParameter → E context}
  {second : (context : Context) → OrbitParameter → F context}

/-- Bounded fixed maps preserve the actual one-high coordinate tower. -/
theorem map (bound : UniformCoordinateBound budget first)
    (smooth : ∀ context, ContDiff ℝ ∞ (first context))
    (mapping : (context : Context) → E context →L[ℝ] F context)
    (constant : ℝ) (nonnegative : 0 ≤ constant) (mappingBound : ∀ context, ‖mapping context‖ ≤ constant) :
    UniformCoordinateBound budget (fun context tau => mapping context (first context tau)) := by
  intro axis order
  obtain ⟨coefficient, coefficientNonnegative, estimate⟩ := bound axis order
  refine ⟨constant * coefficient, mul_nonneg nonnegative coefficientNonnegative, ?_⟩
  intro context base time
  have curveSmooth : ContDiff ℝ ∞ (fun t : ℝ => first context (base + t • axisVector axis)) :=
    (smooth context).comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  rw [← coefficient_iteratedDeriv (mapping context) _ curveSmooth]
  have operatorBound := (mapping context).le_opNorm
    (iteratedDeriv order (fun t : ℝ => first context (base + t • axisVector axis)) time)
  exact operatorBound.trans ((mul_le_mul (mappingBound context) (estimate context base time) (norm_nonneg _) nonnegative).trans_eq (by ring))

/-- A finite sum is handled in the same complete operator norm. -/
theorem add {other : (context : Context) → OrbitParameter → E context}
    (firstBound : UniformCoordinateBound budget first) (otherBound : UniformCoordinateBound budget other)
    (firstSmooth : ∀ context, ContDiff ℝ ∞ (first context))
    (otherSmooth : ∀ context, ContDiff ℝ ∞ (other context)) :
    UniformCoordinateBound budget (fun context tau => first context tau + other context tau) := by
  intro axis order
  obtain ⟨firstConstant, firstNonnegative, firstEstimate⟩ := firstBound axis order
  obtain ⟨otherConstant, otherNonnegative, otherEstimate⟩ := otherBound axis order
  refine ⟨firstConstant + otherConstant, add_nonneg firstNonnegative otherNonnegative, ?_⟩
  intro context base time
  have firstCurve : ContDiff ℝ ∞ (fun t : ℝ => first context (base + t • axisVector axis)) :=
    (firstSmooth context).comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have otherCurve : ContDiff ℝ ∞ (fun t : ℝ => other context (base + t • axisVector axis)) :=
    (otherSmooth context).comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  change ‖iteratedDeriv order ((fun t : ℝ => first context (base + t • axisVector axis)) +
    fun t : ℝ => other context (base + t • axisVector axis)) time‖ ≤ _
  rw [iteratedDeriv_add (firstCurve.contDiffAt.of_le (by exact_mod_cast (show (order : ℕ∞) ≤ ⊤ from le_top)))
    (otherCurve.contDiffAt.of_le (by exact_mod_cast (show (order : ℕ∞) ≤ ⊤ from le_top)))]
  exact (norm_add_le _ _).trans ((add_le_add (firstEstimate context base time) (otherEstimate context base time)).trans_eq (by ring))

/-- The generic bounded bilinear operation may be complex operator
composition while all derivatives remain with respect to real translations. -/
theorem bilinear (firstBound : UniformCoordinateBound budget first) (secondBound : UniformCoordinateBound budget second)
    (firstSmooth : ∀ context, ContDiff ℝ ∞ (first context)) (secondSmooth : ∀ context, ContDiff ℝ ∞ (second context))
    (product : (context : Context) → E context →L[ℝ] F context →L[ℝ] G context)
    (productConstant : ℝ) (productNonnegative : 0 ≤ productConstant) (productBound : ∀ context, ‖product context‖ ≤ productConstant)
    (budgetNonnegative : ∀ context order, 0 ≤ budget context order)
    (pair : ℕ → ℝ) (pairNonnegative : ∀ order, 0 ≤ pair order)
    (paired : ∀ context a b, budget context a * budget context b ≤ pair (a + b) * budget context (a + b)) :
    UniformCoordinateBound budget (fun context tau => product context (first context tau) (second context tau)) := by
  intro axis order
  choose firstConstant firstNonnegative firstEstimate using firstBound axis
  choose secondConstant secondNonnegative secondEstimate using secondBound axis
  by_cases zero : order = 0
  · subst order
    refine ⟨productConstant * firstConstant 0 * secondConstant 0,
      mul_nonneg (mul_nonneg productNonnegative (firstNonnegative 0)) (secondNonnegative 0), ?_⟩
    intro context base time
    simp only [iteratedDeriv_zero, coordinateJetWeight, ↓reduceIte, mul_one] at firstEstimate secondEstimate ⊢
    have firstActual := firstEstimate 0 context base time
    have secondActual := secondEstimate 0 context base time
    simp only [iteratedDeriv_zero, ↓reduceIte, mul_one] at firstActual secondActual
    have outer := (product context).le_opNorm (first context (base + time • axisVector axis))
    have inner := (product context (first context (base + time • axisVector axis))).le_opNorm
      (second context (base + time • axisVector axis))
    exact inner.trans ((mul_le_mul
      (outer.trans (mul_le_mul (productBound context) firstActual (norm_nonneg _) productNonnegative))
      secondActual (norm_nonneg _) (mul_nonneg productNonnegative (firstNonnegative 0))))
  · let constant := ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) *
      firstConstant index * secondConstant (order - index) * (1 + pair order)
    have constantNonnegative : 0 ≤ constant := by
      apply Finset.sum_nonneg
      intro index _
      exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (firstNonnegative index))
        (secondNonnegative _)) (by linarith only [pairNonnegative order])
    refine ⟨productConstant * constant, mul_nonneg productNonnegative constantNonnegative, ?_⟩
    intro context base time
    have firstCurve : ContDiff ℝ ∞ (fun t : ℝ => first context (base + t • axisVector axis)) :=
      (firstSmooth context).comp (contDiff_const.add (contDiff_id.smul contDiff_const))
    have secondCurve : ContDiff ℝ ∞ (fun t : ℝ => second context (base + t • axisVector axis)) :=
      (secondSmooth context).comp (contDiff_const.add (contDiff_id.smul contDiff_const))
    have actual := iteratedDeriv_bilinear_oneHigh (product context) _ _ firstCurve secondCurve
      (budget context) pair firstConstant secondConstant (budgetNonnegative context) pairNonnegative
      firstNonnegative secondNonnegative (paired context) order (Nat.pos_of_ne_zero zero) time
      (fun index _ => firstEstimate index context base time) (fun index _ => secondEstimate index context base time)
    change _ ≤ productConstant * constant * coordinateJetWeight (budget context) order
    rw [coordinateJetWeight, if_neg zero]
    exact actual.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (productBound context) constantNonnegative) (budgetNonnegative context order))
end UniformCoordinateBound
end Grad.AnnularCrossOrbit
