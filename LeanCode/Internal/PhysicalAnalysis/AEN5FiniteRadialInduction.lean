import AEN4ActualSignedCollarEquation

noncomputable section
set_option maxHeartbeats 1400000
open scoped BigOperators
namespace Grad.ExceptionalNative

/-- Strong induction on genuine derivative energy, starting at counts zero
only. Uniform constants are chosen before the family input. -/
theorem firstOrderRadialInduction {Input : Type*} (grade : ℕ)
    (energy forcing : Input → ℕ → ℝ) (size : Input → ℝ)
    (base sourceConstant : ℝ) (product : ℕ → ℝ)
    (sizeNonnegative : ∀ input, 0 ≤ size input) (baseNonnegative : 0 ≤ base)
    (sourceNonnegative : 0 ≤ sourceConstant) (productNonnegative : ∀ order, 0 ≤ product order)
    (baseBound : ∀ input order, order = 0 → energy input order ≤ base * size input)
    (sourceBound : ∀ input order, order ≤ grade → forcing input order ≤ sourceConstant * size input)
    (recurrence : ∀ input order, order ≤ grade → energy input (order + 1) ≤
      4 * (forcing input order + product order * (∑ index ∈ Finset.range (order + 1), energy input (order - index)))) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ input order, order ≤ grade + 1 → energy input order ≤ constant * size input := by
  have individual : ∀ order : ℕ, order ≤ grade + 1 → ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ input, energy input order ≤ constant * size input := by
    intro radial
    induction radial using Nat.strong_induction_on with
    | h radial previous =>
      intro upper
      by_cases small : radial = 0
      · exact ⟨base, baseNonnegative, fun input => baseBound input radial small⟩
      · let order := radial - 1
        have exactOrder : order + 1 = radial := by omega
        have paid : order ≤ grade := by omega
        have previousAll : ∀ index : Fin radial, ∃ constant : ℝ, 0 ≤ constant ∧
            ∀ input, energy input index.val ≤ constant * size input :=
          fun index => previous index.val index.isLt (by omega)
        choose constants nonnegative estimates using previousAll
        let lower (index : ℕ) : ℝ := constants ⟨order - index, by omega⟩
        let result := 4 * (sourceConstant + product order * (∑ index ∈ Finset.range (order + 1), lower index))
        refine ⟨result, ?_, ?_⟩
        · exact mul_nonneg (by norm_num) (add_nonneg sourceNonnegative
            (mul_nonneg (productNonnegative order) (Finset.sum_nonneg (fun _ _ => nonnegative _))))
        · intro input
          have lowerSum : (∑ index ∈ Finset.range (order + 1), energy input (order - index)) ≤
              (∑ index ∈ Finset.range (order + 1), lower index) * size input :=
            (Finset.sum_le_sum (fun index _ => estimates ⟨order - index, by omega⟩ input)).trans_eq
              (Finset.sum_mul _ _ _).symm
          have estimate := (recurrence input order paid).trans ((mul_le_mul_of_nonneg_left
            (add_le_add (sourceBound input order paid)
              (mul_le_mul_of_nonneg_left lowerSum (productNonnegative order))) (by norm_num)).trans_eq
                (show _ = result * size input by dsimp only [result]; ring))
          simpa only [exactOrder] using estimate

  have all : ∀ order : Fin (grade + 2), ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ input, energy input order.val ≤ constant * size input := fun order => individual order.val (by omega)
  choose constants nonnegative estimates using all
  refine ⟨∑ order : Fin (grade + 2), constants order, Finset.sum_nonneg (fun order _ => nonnegative order), ?_⟩
  intro input order upper
  let index : Fin (grade + 2) := ⟨order, by omega⟩
  exact (estimates index input).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun other _ => nonnegative other) (Finset.mem_univ index)) (sizeNonnegative input))

end Grad.ExceptionalNative
