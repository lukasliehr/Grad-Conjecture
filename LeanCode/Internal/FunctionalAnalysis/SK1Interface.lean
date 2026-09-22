import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

noncomputable section

open scoped BigOperators

namespace Grad.SchurKernel.Finite

section Generic

variable {Output Input ValueIn ValueOut : Type*} [Fintype Output] [Fintype Input]
  [NormedAddCommGroup ValueIn] [NormedSpace ℂ ValueIn]
  [NormedAddCommGroup ValueOut] [NormedSpace ℂ ValueOut]

def finiteAction (coefficients : Output → Input → ValueIn →L[ℂ] ValueOut)
    (field : PiLp 2 (fun _ : Input => ValueIn)) : PiLp 2 (fun _ : Output => ValueOut) :=
  WithLp.toLp 2 (fun output => ∑ input : Input, coefficients output input (field input))

def sumSquaresGoal : Prop :=
  ∀ (coefficients : Output → Input → ValueIn →L[ℂ] ValueOut)
    (majorant : Output → Input → ℝ) (rowBound columnBound : ℝ),
    0 ≤ rowBound → 0 ≤ columnBound →
    (∀ output input, 0 ≤ majorant output input) →
    (∀ output input, ‖coefficients output input‖ ≤ majorant output input) →
    (∀ output, ∑ input : Input, majorant output input ≤ rowBound) →
    (∀ input, ∑ output : Output, majorant output input ≤ columnBound) →
    ∀ field : PiLp 2 (fun _ : Input => ValueIn),
      ∑ output : Output, ‖finiteAction coefficients field output‖ ^ 2 ≤
        rowBound * columnBound * ∑ input : Input, ‖field input‖ ^ 2

def normGoal : Prop :=
  ∀ (coefficients : Output → Input → ValueIn →L[ℂ] ValueOut)
    (majorant : Output → Input → ℝ) (rowBound columnBound : ℝ),
    0 ≤ rowBound → 0 ≤ columnBound →
    (∀ output input, 0 ≤ majorant output input) →
    (∀ output input, ‖coefficients output input‖ ≤ majorant output input) →
    (∀ output, ∑ input : Input, majorant output input ≤ rowBound) →
    (∀ input, ∑ output : Output, majorant output input ≤ columnBound) →
    ∀ field : PiLp 2 (fun _ : Input => ValueIn),
      ‖finiteAction coefficients field‖ ≤ Real.sqrt (rowBound * columnBound) * ‖field‖

def constructorGoal : Prop :=
  ∀ (coefficients : Output → Input → ValueIn →L[ℂ] ValueOut)
    (majorant : Output → Input → ℝ) (rowBound columnBound : ℝ),
    0 ≤ rowBound → 0 ≤ columnBound →
    (∀ output input, 0 ≤ majorant output input) →
    (∀ output input, ‖coefficients output input‖ ≤ majorant output input) →
    (∀ output, ∑ input : Input, majorant output input ≤ rowBound) →
    (∀ input, ∑ output : Output, majorant output input ≤ columnBound) →
    ∃ boundedMap : PiLp 2 (fun _ : Input => ValueIn) →L[ℂ]
        PiLp 2 (fun _ : Output => ValueOut),
      ‖boundedMap‖ ≤ Real.sqrt (rowBound * columnBound) ∧
      (∀ field, boundedMap field = finiteAction coefficients field) ∧
      (∀ field output, boundedMap field output =
        ∑ input : Input, coefficients output input (field input))

end Generic

def physicalConsumerGoal : Prop :=
  ∀ (outputs inputs : Finset ℤ)
    (coefficients : outputs → inputs → EuclideanSpace ℂ (Fin 3) →L[ℂ]
      EuclideanSpace ℂ (Fin 3))
    (majorant : outputs → inputs → ℝ) (rowBound columnBound : ℝ),
    0 ≤ rowBound → 0 ≤ columnBound →
    (∀ output input, 0 ≤ majorant output input) →
    (∀ output input, ‖coefficients output input‖ ≤ majorant output input) →
    (∀ output, ∑ input : inputs, majorant output input ≤ rowBound) →
    (∀ input, ∑ output : outputs, majorant output input ≤ columnBound) →
    (∀ field : PiLp 2 (fun _ : inputs => EuclideanSpace ℂ (Fin 3)),
      ∑ output : outputs, ‖∑ input : inputs, coefficients output input (field input)‖ ^ 2 ≤
        rowBound * columnBound * ∑ input : inputs, ‖field input‖ ^ 2) ∧
    ∃ boundedMap : PiLp 2 (fun _ : inputs => EuclideanSpace ℂ (Fin 3)) →L[ℂ]
        PiLp 2 (fun _ : outputs => EuclideanSpace ℂ (Fin 3)),
      ‖boundedMap‖ ≤ Real.sqrt (rowBound * columnBound) ∧
      (∀ field output, boundedMap field output =
        ∑ input : inputs, coefficients output input (field input))

end Grad.SchurKernel.Finite
