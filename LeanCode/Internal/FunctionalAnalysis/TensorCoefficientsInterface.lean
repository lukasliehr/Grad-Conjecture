import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

open scoped BigOperators

namespace Grad.TensorCoefficients

noncomputable section

def tensorCoefficient (rank : ℕ) (coefficients : Fin 2 → Fin 2 → ℝ)
    (output input : Fin rank → Fin 2) : ℝ :=
  ∏ position, coefficients (input position) (output position)

def rowOrthogonality (coefficients : Fin 2 → Fin 2 → ℝ) : Prop :=
  ∀ first second : Fin 2,
    ∑ index : Fin 2, coefficients first index * coefficients second index =
      if first = second then 1 else 0

def coefficientOrthogonalityGoal (rank : ℕ)
    (coefficients : Fin 2 → Fin 2 → ℝ) : Prop :=
  rowOrthogonality coefficients →
    ∀ first second : Fin rank → Fin 2,
      ∑ output : Fin rank → Fin 2,
          tensorCoefficient rank coefficients output first *
            tensorCoefficient rank coefficients output second =
        if first = second then 1 else 0

def universalOrthogonalityGoal : Prop :=
  ∀ (rank : ℕ) (coefficients : Fin 2 → Fin 2 → ℝ),
    coefficientOrthogonalityGoal rank coefficients

end

end Grad.TensorCoefficients
