import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic

noncomputable section

namespace Grad.MainAssembly.TensorAngleRigidity

open Matrix

/-- Exact two-part `NG_R06` public contract. -/
def TensorAngleCongruenceGoal
    (normalizedShape : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (normalSignMatrix : ℝ → Matrix (Fin 2) (Fin 2) ℝ) :
    Prop :=
  (∀ rho first second, 0 < rho →
    (normalizedShape rho second = normalizedShape rho first ↔
      ∃ integer : ℤ, second - first = (integer : ℝ) * Real.pi)) ∧
  ∀ rho angle normalSign,
    (normalSign = 1 ∨ normalSign = -1) →
    normalSignMatrix normalSign * normalizedShape rho angle *
        (normalSignMatrix normalSign)ᵀ =
      normalizedShape rho (normalSign * angle)

end Grad.MainAssembly.TensorAngleRigidity
