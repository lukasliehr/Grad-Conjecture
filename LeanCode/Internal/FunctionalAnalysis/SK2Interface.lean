import WeakH1
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section

open scoped BigOperators

namespace Grad.SchurKernel.Discrete

def discreteAction {ValueIn ValueOut : Type*}
    [NormedAddCommGroup ValueIn] [NormedSpace ℂ ValueIn]
    [NormedAddCommGroup ValueOut] [NormedSpace ℂ ValueOut]
    (coefficients : ℤ → ℤ → ValueIn →L[ℂ] ValueOut)
    (field : lp (fun _ : ℤ => ValueIn) 2) (output : ℤ) : ValueOut :=
  ∑' input : ℤ, coefficients output input (field input)

def blockGoal {ValueIn ValueOut : Type*}
    [NormedAddCommGroup ValueIn] [NormedSpace ℂ ValueIn]
    [NormedAddCommGroup ValueOut] [NormedSpace ℂ ValueOut]
    [_complete : CompleteSpace ValueOut] : Prop :=
  ∀ (coefficients : ℤ → ℤ → ValueIn →L[ℂ] ValueOut)
    (majorant : ℤ → ℤ → ℝ) (rowBound columnBound : ℝ),
    0 ≤ rowBound → 0 ≤ columnBound →
    (∀ output input, 0 ≤ majorant output input) →
    (∀ output input, ‖coefficients output input‖ ≤ majorant output input) →
    (∀ output, Summable (majorant output)) →
    (∀ input, Summable (fun output => majorant output input)) →
    (∀ output, ∑' input : ℤ, majorant output input ≤ rowBound) →
    (∀ input, ∑' output : ℤ, majorant output input ≤ columnBound) →
    (∀ (field : lp (fun _ : ℤ => ValueIn) 2) (output : ℤ),
      Summable (fun input : ℤ => ‖coefficients output input (field input)‖) ∧
      Summable (fun input : ℤ => coefficients output input (field input))) ∧
    (∀ field : lp (fun _ : ℤ => ValueIn) 2, Memℓp (discreteAction coefficients field) 2) ∧
    (∀ field : lp (fun _ : ℤ => ValueIn) 2,
      ∑' output : ℤ, ‖discreteAction coefficients field output‖ ^ 2 ≤
        rowBound * columnBound * ∑' input : ℤ, ‖field input‖ ^ 2) ∧
    ∃ boundedMap : lp (fun _ : ℤ => ValueIn) 2 →L[ℂ] lp (fun _ : ℤ => ValueOut) 2,
      ‖boundedMap‖ ≤ Real.sqrt (rowBound * columnBound) ∧
      (∀ (field : lp (fun _ : ℤ => ValueIn) 2) (output : ℤ),
        boundedMap field output = ∑' input : ℤ, coefficients output input (field input)) ∧
      (∀ field, ‖boundedMap field‖ ^ 2 ≤ rowBound * columnBound * ‖field‖ ^ 2) ∧
      (∀ field, ‖boundedMap field‖ ≤ Real.sqrt (rowBound * columnBound) * ‖field‖) ∧
      (∀ first second, boundedMap (first + second) = boundedMap first + boundedMap second) ∧
      (∀ (scalar : ℂ) field, boundedMap (scalar • field) = scalar • boundedMap field)

def physicalConsumerGoal : Prop :=
  ∀ (coefficients : ℤ → ℤ → EuclideanSpace ℂ (Fin 3) →L[ℂ] EuclideanSpace ℂ (Fin 3))
    (majorant : ℤ → ℤ → ℝ) (rowBound columnBound : ℝ),
    0 ≤ rowBound → 0 ≤ columnBound →
    (∀ output input, 0 ≤ majorant output input) →
    (∀ output input, ‖coefficients output input‖ ≤ majorant output input) →
    (∀ output, Summable (majorant output)) →
    (∀ input, Summable (fun output => majorant output input)) →
    (∀ output, ∑' input : ℤ, majorant output input ≤ rowBound) →
    (∀ input, ∑' output : ℤ, majorant output input ≤ columnBound) →
    (∀ (field : Grad.PDEBootstrap.CellValues) (output : ℤ),
      Summable (fun input : ℤ => ‖coefficients output input (field input)‖) ∧
      Summable (fun input : ℤ => coefficients output input (field input))) ∧
    (∀ field : Grad.PDEBootstrap.CellValues,
      Memℓp (fun output : ℤ => ∑' input : ℤ, coefficients output input (field input)) 2) ∧
    (∀ field : Grad.PDEBootstrap.CellValues,
      ∑' output : ℤ, ‖∑' input : ℤ, coefficients output input (field input)‖ ^ 2 ≤
        rowBound * columnBound * ∑' input : ℤ, ‖field input‖ ^ 2) ∧
    ∃ boundedMap : Grad.PDEBootstrap.CellValues →L[ℂ] Grad.PDEBootstrap.CellValues,
      ‖boundedMap‖ ≤ Real.sqrt (rowBound * columnBound) ∧
      (∀ (field : Grad.PDEBootstrap.CellValues) (output : ℤ),
        boundedMap field output = ∑' input : ℤ, coefficients output input (field input)) ∧
      (∀ field, ‖boundedMap field‖ ^ 2 ≤ rowBound * columnBound * ‖field‖ ^ 2) ∧
      (∀ field, ‖boundedMap field‖ ≤ Real.sqrt (rowBound * columnBound) * ‖field‖) ∧
      (∀ first second, boundedMap (first + second) = boundedMap first + boundedMap second) ∧
      (∀ (scalar : ℂ) field, boundedMap (scalar • field) = scalar • boundedMap field)

end Grad.SchurKernel.Discrete
