import AOD5WeightedRecurrence

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Grad.CircularHighRegularity

/-- Strong induction for a family of actual mode energies. The constant
is chosen before the input, so it is uniform in source and parameter. -/
theorem finiteRadialInduction {Input : Type*} (grade : ℕ)
    (energy forcing : Input → ℕ → ℤ → ℝ) (size : Input → ℝ)
    (allowed : ℤ → Prop) (base forcingConstant ceiling : ℝ) (product : ℕ → ℝ)
    (sizeNonnegative : ∀ input, 0 ≤ size input) (baseNonnegative : 0 ≤ base)
    (forcingNonnegative : 0 ≤ forcingConstant) (productNonnegative : ∀ order, 0 ≤ product order)
    (baseBound : ∀ input radial, radial ≤ 2 → ∀ modes : Finset ℤ,
      (∀ mode ∈ modes, allowed mode) → (∑ mode ∈ modes, energy input radial mode) ≤ base * size input)
    (forcingBound : ∀ input order, order ≤ grade → ∀ modes : Finset ℤ,
      (∀ mode ∈ modes, allowed mode) → (∑ mode ∈ modes, forcing input order mode) ≤ forcingConstant * size input)
    (recurrence : ∀ input order, order ≤ grade → ∀ mode, allowed mode →
      energy input (order + 2) mode ≤ 4 *
        (product order * (∑ index ∈ Finset.range (order + 1), energy input (order - index + 1) mode) +
          product order * (∑ index ∈ Finset.range (order + 1), energy input (order - index) mode) +
          ceiling ^ 4 * energy input order mode + forcing input order mode)) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ input radial, radial ≤ grade + 2 → ∀ modes : Finset ℤ,
      (∀ mode ∈ modes, allowed mode) → (∑ mode ∈ modes, energy input radial mode) ≤ constant * size input := by
  classical
  have individual : ∀ radial : ℕ, radial ≤ grade + 2 → ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ input modes, (∀ mode ∈ modes, allowed mode) →
        (∑ mode ∈ modes, energy input radial mode) ≤ constant * size input := by
    intro radial
    induction radial using Nat.strong_induction_on with
    | h radial previous =>
      intro upper
      by_cases small : radial ≤ 2
      · exact ⟨base, baseNonnegative, fun input modes high => baseBound input radial small modes high⟩
      · let order := radial - 2
        have exactOrder : order + 2 = radial := by omega
        have paid : order ≤ grade := by omega
        have previousAll : ∀ index : Fin radial, ∃ constant : ℝ, 0 ≤ constant ∧
            ∀ input modes, (∀ mode ∈ modes, allowed mode) →
              (∑ mode ∈ modes, energy input index.val mode) ≤ constant * size input :=
          fun index => previous index.val index.isLt (by omega)
        choose constants constantsNonnegative estimates using previousAll
        let firstConstant (index : ℕ) : ℝ := constants ⟨order - index + 1, by omega⟩
        let secondConstant (index : ℕ) : ℝ := constants ⟨order - index, by omega⟩
        let middleConstant : ℝ := constants ⟨order, by omega⟩
        let result : ℝ := 4 * (product order * (∑ index ∈ Finset.range (order + 1), firstConstant index) +
          product order * (∑ index ∈ Finset.range (order + 1), secondConstant index) +
          ceiling ^ 4 * middleConstant + forcingConstant)
        refine ⟨result, ?_, ?_⟩
        · exact mul_nonneg (by norm_num) (add_nonneg (add_nonneg (add_nonneg
            (mul_nonneg (productNonnegative order) (Finset.sum_nonneg (fun _ _ => constantsNonnegative _)))
            (mul_nonneg (productNonnegative order) (Finset.sum_nonneg (fun _ _ => constantsNonnegative _))))
            (mul_nonneg (by positivity) (constantsNonnegative _))) forcingNonnegative)
        · intro input modes high
          have modeRec (mode : ℤ) (member : mode ∈ modes) := recurrence input order paid mode (high mode member)
          have firstBounds (index : ℕ) (_member : index ∈ Finset.range (order + 1)) :
              (∑ mode ∈ modes, energy input (order - index + 1) mode) ≤ firstConstant index * size input :=
            estimates ⟨order - index + 1, by omega⟩ input modes high
          have secondBounds (index : ℕ) (_member : index ∈ Finset.range (order + 1)) :
              (∑ mode ∈ modes, energy input (order - index) mode) ≤ secondConstant index * size input :=
            estimates ⟨order - index, by omega⟩ input modes high
          have firstSum : (∑ mode ∈ modes, ∑ index ∈ Finset.range (order + 1), energy input (order - index + 1) mode) ≤
              (∑ index ∈ Finset.range (order + 1), firstConstant index) * size input := by
            rw [Finset.sum_comm]
            exact (Finset.sum_le_sum firstBounds).trans_eq (Finset.sum_mul _ _ _).symm
          have secondSum : (∑ mode ∈ modes, ∑ index ∈ Finset.range (order + 1), energy input (order - index) mode) ≤
              (∑ index ∈ Finset.range (order + 1), secondConstant index) * size input := by
            rw [Finset.sum_comm]
            exact (Finset.sum_le_sum secondBounds).trans_eq (Finset.sum_mul _ _ _).symm
          have middleBound := estimates ⟨order, by omega⟩ input modes high
          have sourceBound := forcingBound input order paid modes high
          have summed := Finset.sum_le_sum modeRec
          simp only [← Finset.mul_sum, Finset.sum_add_distrib] at summed
          have finalBound : (∑ mode ∈ modes, energy input (order + 2) mode) ≤ result * size input := summed.trans ((mul_le_mul_of_nonneg_left
            (add_le_add (add_le_add (add_le_add
              (mul_le_mul_of_nonneg_left firstSum (productNonnegative order))
              (mul_le_mul_of_nonneg_left secondSum (productNonnegative order)))
              (mul_le_mul_of_nonneg_left middleBound (by positivity : 0 ≤ ceiling ^ 4))) sourceBound)
            (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by dsimp only [result, middleConstant]; ring))
          simpa only [exactOrder] using finalBound
  have every : ∀ radial : Fin (grade + 3), ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ input modes, (∀ mode ∈ modes, allowed mode) →
        (∑ mode ∈ modes, energy input radial.val mode) ≤ constant * size input :=
    fun radial => individual radial.val (by omega)
  choose constants nonnegative estimates using every
  refine ⟨∑ radial : Fin (grade + 3), constants radial, Finset.sum_nonneg (fun radial _ => nonnegative radial), ?_⟩
  intro input radial upper modes high
  let index : Fin (grade + 3) := ⟨radial, by omega⟩
  have constantBound := Finset.single_le_sum (s := Finset.univ) (f := constants)
    (fun radial _ => nonnegative radial) (Finset.mem_univ index)
  exact (estimates index input modes high).trans (mul_le_mul_of_nonneg_right constantBound (sizeNonnegative input))

end Grad.CircularHighRegularity
