import TensorCoefficientsInterface

open scoped BigOperators

namespace Grad.TensorCoefficients.Composition

noncomputable section

def productCoefficients (first second : Fin 2 → Fin 2 → ℝ)
    (input output : Fin 2) : ℝ :=
  ∑ middle : Fin 2, second input middle * first middle output

def coefficientCompositionGoal (rank : ℕ)
    (first second : Fin 2 → Fin 2 → ℝ) : Prop :=
  ∀ output input : Fin rank → Fin 2,
    tensorCoefficient rank (productCoefficients first second) output input =
      ∑ middleWord : Fin rank → Fin 2,
        tensorCoefficient rank first output middleWord *
          tensorCoefficient rank second middleWord input

def universalCompositionGoal : Prop :=
  ∀ (rank : ℕ) (first second : Fin 2 → Fin 2 → ℝ),
    coefficientCompositionGoal rank first second

end

end Grad.TensorCoefficients.Composition
