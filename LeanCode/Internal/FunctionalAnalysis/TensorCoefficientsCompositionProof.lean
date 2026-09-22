import TensorCoefficientsCompositionInterface

open scoped BigOperators

namespace Grad.TensorCoefficients.Composition

theorem tensorCoefficient_composition
    (rank : ℕ) (first second : Fin 2 → Fin 2 → ℝ)
    (output input : Fin rank → Fin 2) :
    tensorCoefficient rank (productCoefficients first second) output input =
      ∑ middleWord : Fin rank → Fin 2,
        tensorCoefficient rank first output middleWord *
          tensorCoefficient rank second middleWord input := by
  unfold tensorCoefficient productCoefficients
  calc
    (∏ position, ∑ middle : Fin 2,
        second (input position) middle * first middle (output position)) =
        ∑ middleWord : Fin rank → Fin 2,
          ∏ position, second (input position) (middleWord position) *
            first (middleWord position) (output position) :=
      Fintype.prod_sum (ι := Fin rank) (κ := fun _ => Fin 2)
        (fun position middle => second (input position) middle *
          first middle (output position))
    _ = ∑ middleWord : Fin rank → Fin 2,
        (∏ position, first (middleWord position) (output position)) *
          (∏ position, second (input position) (middleWord position)) := by
      apply Finset.sum_congr rfl
      intro middleWord _
      calc
        (∏ position, second (input position) (middleWord position) *
            first (middleWord position) (output position)) =
            (∏ position, second (input position) (middleWord position)) *
              (∏ position, first (middleWord position) (output position)) :=
          Finset.prod_mul_distrib
        _ = (∏ position, first (middleWord position) (output position)) *
            (∏ position, second (input position) (middleWord position)) :=
          mul_comm _ _

theorem universalComposition : universalCompositionGoal :=
  tensorCoefficient_composition

end Grad.TensorCoefficients.Composition
