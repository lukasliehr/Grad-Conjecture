import AJD27OriginalCoupledBudgetContexts
import AJD33UniformOperatorComposition

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped ContDiff
namespace Grad.AnnularHighGenerators
open Grad.AnnularKernelOrbit Grad.AnnularCrossOrbit Grad.AnnularOrbitGenerators Grad.AnnularInverseCalculus
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularHighInverseOrbit

/-- The harmless constant part of source coefficients is retained explicitly.
It will be absorbed by the top data grade in the final tame estimate. -/
def augmentedBudget {Context : Type*} (budget : Context → ℕ → ℝ) (context : Context) (order : ℕ) : ℝ :=
  1 + budget context order

theorem augmentedBudget_pair {Context : Type*} (budget : Context → ℕ → ℝ)
    (_nonnegative : ∀ context order, 0 ≤ budget context order)
    (monotone : ∀ context, Monotone (budget context))
    (pair : ℕ → ℝ) (pairNonnegative : ∀ order, 0 ≤ pair order)
    (paired : ∀ context a b, budget context a * budget context b ≤ pair (a + b) * budget context (a + b))
    (context : Context) (a b : ℕ) :
    augmentedBudget budget context a * augmentedBudget budget context b ≤
      (2 + pair (a + b)) * augmentedBudget budget context (a + b) := by
  have first := monotone context (Nat.le_add_right a b)
  have second := monotone context (Nat.le_add_left b a)
  have product := paired context a b
  have coefficient := pairNonnegative (a + b)
  unfold augmentedBudget
  nlinarith

section Uniform
variable {Context : Type*} {E : Context → Type*}
  [∀ context, NormedAddCommGroup (E context)] [∀ context, NormedSpace ℝ (E context)]

/-- Enlarging only the positive-order budget preserves the genuine derivative estimate. -/
theorem uniformCoordinateBound_augment (budget : Context → ℕ → ℝ)
    (family : (context : Context) → OrbitParameter → E context)
    (bound : UniformCoordinateBound budget family) :
    UniformCoordinateBound (augmentedBudget budget) family := by
  intro axis order
  obtain ⟨constant, nonnegative, estimate⟩ := bound axis order
  refine ⟨constant, nonnegative, ?_⟩
  intro context base time
  apply (estimate context base time).trans
  apply mul_le_mul_of_nonneg_left _ nonnegative
  unfold coordinateJetWeight augmentedBudget
  split_ifs <;> linarith

/-- Actual two-column Fréchet towers give the actual derivative along every
translated angular or cell line, uniformly before its physical context. -/
theorem uniformCoordinateBound_of_realJet
    (budget : Context → ℕ → ℝ) (jet : (context : Context) → ℕ → ℕ → OrbitParameter → E context)
    (derivative : ∀ context angular cell point, HasFDerivAt (jet context angular cell)
      (orbitColumns (jet context (angular + 1) cell point) (jet context angular (cell + 1) point)) point)
    (bound : ∀ angular cell, ∃ constant : ℝ, 0 ≤ constant ∧ ∀ context point,
      ‖jet context angular cell point‖ ≤ constant * coordinateJetWeight (budget context) (angular + cell)) :
    UniformCoordinateBound budget (fun context => jet context 0 0) := by
  intro axis order
  obtain ⟨constant, nonnegative, estimate⟩ := bound (if axis then 0 else order) (if axis then order else 0)
  refine ⟨constant, nonnegative, ?_⟩
  intro context base time
  rw [iteratedDeriv_coordinateJet (jet context) (derivative context)]
  cases axis <;> simpa only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero] using
    estimate context (base + time • axisVector _)
end Uniform

variable (parameters : Grad.CartesianState.PhaseParameters) (L compact : ℝ)

theorem coupledAugmentedBudget_nonnegative
    (context : CoupledCoordinateContext parameters L compact) (order : ℕ) :
    0 ≤ augmentedBudget CoupledCoordinateContext.budget context order :=
  add_nonneg zero_le_one (context.budget_nonnegative order)

theorem coupledAugmentedBudget_pair
    (context : CoupledCoordinateContext parameters L compact) (a b : ℕ) :
    augmentedBudget CoupledCoordinateContext.budget context a * augmentedBudget CoupledCoordinateContext.budget context b ≤
      (2 + pairBudgetConstant 8 (a + b) 1) * augmentedBudget CoupledCoordinateContext.budget context (a + b) :=
  augmentedBudget_pair CoupledCoordinateContext.budget CoupledCoordinateContext.budget_nonnegative
    CoupledCoordinateContext.budget_monotone (fun order => pairBudgetConstant 8 order 1)
    (fun order => pairBudgetConstant_nonnegative 8 order (by norm_num))
    CoupledCoordinateContext.budget_pair context a b

end Grad.AnnularHighGenerators
