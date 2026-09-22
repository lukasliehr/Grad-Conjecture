import ProductPhaseDerivative

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearProduct

open Grad.CartesianState

/-- It suffices to assign the residual frequency power to one input. This
coarse finite allocation keeps its exact total order. -/
theorem sum_frequency_power_le {arity : ℕ} (positiveArity : 0 < arity)
    (cells : Fin arity → ℤ) (power : ℕ) :
    productFrequency cells ^ power ≤ (arity : ℝ) ^ power *
      ∑ index, cellFrequency (cells index) ^ power := by
  classical
  obtain ⟨largest, _, maximal⟩ := Finset.exists_max_image Finset.univ
    (fun index : Fin arity => cellFrequency (cells index))
    ⟨⟨0, positiveArity⟩, Finset.mem_univ _⟩
  have sumBound : productFrequency cells ≤ (arity : ℝ) * cellFrequency (cells largest) := by
    calc
      _ ≤ ∑ _index : Fin arity, cellFrequency (cells largest) :=
        Finset.sum_le_sum (fun index membership => maximal index membership)
      _ = _ := by simp
  calc
    _ ≤ ((arity : ℝ) * cellFrequency (cells largest)) ^ power :=
      pow_le_pow_left₀ (productFrequency_nonnegative cells) sumBound power
    _ = (arity : ℝ) ^ power * cellFrequency (cells largest) ^ power := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun index _ => pow_nonneg (cellFrequency_pos _).le power)
        (Finset.mem_univ largest)) (pow_nonneg (Nat.cast_nonneg _) power)

theorem residual_frequency_bound {arity : ℕ} (positiveArity : 0 < arity)
    (cells : Fin arity → ℤ) (grade order defect derivatives : ℕ)
    (orderBound : order ≤ grade) (allocation : defect + derivatives = order) :
    cellFrequency (∑ index, cells index) ^ (grade - order) * productFrequency cells ^ defect ≤
      (arity : ℝ) ^ (grade - derivatives) *
        ∑ index, cellFrequency (cells index) ^ (grade - derivatives) := by
  calc
    _ ≤ productFrequency cells ^ (grade - order) * productFrequency cells ^ defect :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (cellFrequency_pos _).le (cellFrequency_sum_le positiveArity cells) _)
        (pow_nonneg (productFrequency_nonnegative cells) _)
    _ = productFrequency cells ^ (grade - derivatives) := by
      rw [← pow_add]
      congr 1
      omega
    _ ≤ _ := sum_frequency_power_le positiveArity cells _

end Grad.NonlinearProduct
