import ACB11OriginalProfileEnergies

noncomputable section
set_option maxHeartbeats 1400000
open scoped BigOperators
namespace Grad.ActualCenterBounds

/-- Strong induction on genuine derivative energy, starting at counts zero
and one. Uniform constants are chosen before the family input. -/
theorem centerRadialInduction {Input : Type*} (grade : ℕ)
    (energy forcing : Input → ℕ → ℝ) (size : Input → ℝ)
    (base sourceConstant ceiling : ℝ) (product : ℕ → ℝ)
    (sizeNonnegative : ∀ input, 0 ≤ size input) (baseNonnegative : 0 ≤ base)
    (sourceNonnegative : 0 ≤ sourceConstant) (productNonnegative : ∀ order, 0 ≤ product order)
    (baseBound : ∀ input order, order ≤ 1 → energy input order ≤ base * size input)
    (sourceBound : ∀ input order, order ≤ grade → forcing input order ≤ sourceConstant * size input)
    (recurrence : ∀ input order, order ≤ grade → energy input (order + 2) ≤
      4 * (product order * (∑ index ∈ Finset.range (order + 1), energy input (order - index + 1)) +
        product order * (∑ index ∈ Finset.range (order + 1), energy input (order - index)) +
        ceiling ^ 2 * energy input order + forcing input order)) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ input order, order ≤ grade + 2 → energy input order ≤ constant * size input := by
  have individual : ∀ order : ℕ, order ≤ grade + 2 → ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ input, energy input order ≤ constant * size input := by
    intro radial
    induction radial using Nat.strong_induction_on with
    | h radial previous =>
      intro upper
      by_cases small : radial ≤ 1
      · exact ⟨base, baseNonnegative, fun input => baseBound input radial small⟩
      · let order := radial - 2
        have exactOrder : order + 2 = radial := by omega
        have paid : order ≤ grade := by omega
        have previousAll : ∀ index : Fin radial, ∃ constant : ℝ, 0 ≤ constant ∧
            ∀ input, energy input index.val ≤ constant * size input :=
          fun index => previous index.val index.isLt (by omega)
        choose constants nonnegative estimates using previousAll
        let first (index : ℕ) : ℝ := constants ⟨order - index + 1, by omega⟩
        let second (index : ℕ) : ℝ := constants ⟨order - index, by omega⟩
        let middle : ℝ := constants ⟨order, by omega⟩
        let result := 4 * (product order * (∑ index ∈ Finset.range (order + 1), first index) +
          product order * (∑ index ∈ Finset.range (order + 1), second index) + ceiling ^ 2 * middle + sourceConstant)
        refine ⟨result, ?_, ?_⟩
        · exact mul_nonneg (by norm_num) (add_nonneg (add_nonneg (add_nonneg
            (mul_nonneg (productNonnegative order) (Finset.sum_nonneg (fun _ _ => nonnegative _)))
            (mul_nonneg (productNonnegative order) (Finset.sum_nonneg (fun _ _ => nonnegative _))))
            (mul_nonneg (sq_nonneg _) (nonnegative _))) sourceNonnegative)
        · intro input
          have firstSum : (∑ index ∈ Finset.range (order + 1), energy input (order - index + 1)) ≤
              (∑ index ∈ Finset.range (order + 1), first index) * size input :=
            (Finset.sum_le_sum (fun index _ => estimates ⟨order - index + 1, by omega⟩ input)).trans_eq
              (Finset.sum_mul _ _ _).symm
          have secondSum : (∑ index ∈ Finset.range (order + 1), energy input (order - index)) ≤
              (∑ index ∈ Finset.range (order + 1), second index) * size input :=
            (Finset.sum_le_sum (fun index _ => estimates ⟨order - index, by omega⟩ input)).trans_eq
              (Finset.sum_mul _ _ _).symm
          have estimate := (recurrence input order paid).trans ((mul_le_mul_of_nonneg_left
            (add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left firstSum (productNonnegative order))
              (mul_le_mul_of_nonneg_left secondSum (productNonnegative order)))
              (mul_le_mul_of_nonneg_left (estimates ⟨order, by omega⟩ input) (sq_nonneg ceiling)))
              (sourceBound input order paid)) (by norm_num)).trans_eq
                (show _ = result * size input by dsimp only [result, middle]; ring))
          simpa only [exactOrder] using estimate
  have all : ∀ order : Fin (grade + 3), ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ input, energy input order.val ≤ constant * size input := fun order => individual order.val (by omega)
  choose constants nonnegative estimates using all
  refine ⟨∑ order : Fin (grade + 3), constants order, Finset.sum_nonneg (fun order _ => nonnegative order), ?_⟩
  intro input order upper
  let index : Fin (grade + 3) := ⟨order, by omega⟩
  exact (estimates index input).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun other _ => nonnegative other) (Finset.mem_univ index)) (sizeNonnegative input))

end Grad.ActualCenterBounds
