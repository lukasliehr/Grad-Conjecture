import TensorCoefficientsInterface

open scoped BigOperators

namespace Grad.TensorCoefficients

theorem tensorCoefficient_orthogonality
    (rank : ℕ) (coefficients : Fin 2 → Fin 2 → ℝ)
    (rows : rowOrthogonality coefficients)
    (first second : Fin rank → Fin 2) :
    ∑ output : Fin rank → Fin 2,
        tensorCoefficient rank coefficients output first *
          tensorCoefficient rank coefficients output second =
      if first = second then 1 else 0 := by
  classical
  unfold tensorCoefficient
  calc
    ∑ output : Fin rank → Fin 2,
        (∏ position, coefficients (first position) (output position)) *
          (∏ position, coefficients (second position) (output position)) =
        ∑ output : Fin rank → Fin 2,
          ∏ position, coefficients (first position) (output position) *
            coefficients (second position) (output position) := by
      apply Finset.sum_congr rfl
      intro output _
      exact Finset.prod_mul_distrib.symm
    _ = ∏ position : Fin rank,
        ∑ index : Fin 2,
          coefficients (first position) index * coefficients (second position) index :=
      (Fintype.prod_sum (ι := Fin rank) (κ := fun _ => Fin 2)
        (fun position index => coefficients (first position) index *
          coefficients (second position) index)).symm
    _ = ∏ position : Fin rank,
        (if first position = second position then 1 else 0 : ℝ) := by
      apply Finset.prod_congr rfl
      intro position _
      exact rows (first position) (second position)
    _ = if first = second then 1 else 0 := by
      simpa only [← funext_iff] using
        (Fintype.prod_boole (M₀ := ℝ)
          (p := fun position => first position = second position))

theorem universalOrthogonality : universalOrthogonalityGoal :=
  tensorCoefficient_orthogonality

end Grad.TensorCoefficients
