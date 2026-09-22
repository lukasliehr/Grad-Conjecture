import WTCInterface

noncomputable section

namespace Grad.WeakTesting.Commutation

theorem sameCounts_refl {rank : ℕ} (word : Fin rank → Fin 2) : SameCounts word word :=
  fun _ => rfl

theorem sameCounts_symm {rank : ℕ} {first second : Fin rank → Fin 2}
    (same : SameCounts first second) : SameCounts second first :=
  fun direction => (same direction).symm

theorem sameCounts_permutation {rank : ℕ} (word : Fin rank → Fin 2)
    (permutation : Equiv.Perm (Fin rank)) : SameCounts (word ∘ permutation) word := by
  intro direction
  let fiberEquiv : {position : Fin rank // (word ∘ permutation) position = direction} ≃
      {position : Fin rank // word position = direction} :=
    { toFun := fun position => ⟨permutation position.val, position.property⟩
      invFun := fun position => ⟨permutation.symm position.val, by simpa using position.property⟩
      left_inv := fun position => Subtype.ext (permutation.symm_apply_apply position.val)
      right_inv := fun position => Subtype.ext (permutation.apply_symm_apply position.val) }
  exact Fintype.card_congr fiberEquiv

theorem wordPermutation : WordPermutationGoal := by
  intro rank first second same
  let fibers (direction : Fin 2) :
      {position : Fin rank // second position = direction} ≃
        {position : Fin rank // first position = direction} :=
    Fintype.equivOfCardEq (same direction).symm
  refine ⟨Equiv.ofFiberEquiv fibers, ?_⟩
  funext position
  exact (Equiv.ofFiberEquiv_map fibers position).symm

theorem sameCounts_iff_permutation {rank : ℕ} (first second : Fin rank → Fin 2) :
    SameCounts first second ↔
      ∃ permutation : Equiv.Perm (Fin rank), second = first ∘ permutation := by
  constructor
  · exact wordPermutation rank first second
  · rintro ⟨permutation, rfl⟩
    exact sameCounts_symm (sameCounts_permutation first permutation)

theorem canonicalWord_eq_zero (zeros ones : ℕ) (position : Fin (zeros + ones)) :
    canonicalWord zeros ones position = 0 ↔ position.val < zeros := by
  simp only [canonicalWord]
  split_ifs <;> simp_all

theorem canonicalWord_eq_one (zeros ones : ℕ) (position : Fin (zeros + ones)) :
    canonicalWord zeros ones position = 1 ↔ zeros ≤ position.val := by
  simp only [canonicalWord]
  split_ifs <;> simp_all

theorem canonicalWord_count_zero (zeros ones : ℕ) :
    directionCount (canonicalWord zeros ones) 0 = zeros := by
  let fiberEquiv : {position : Fin (zeros + ones) // canonicalWord zeros ones position = 0} ≃
      Fin zeros :=
    { toFun := fun position =>
        ⟨position.val.val, (canonicalWord_eq_zero zeros ones position.val).mp position.property⟩
      invFun := fun position =>
        ⟨⟨position.val, by omega⟩, (canonicalWord_eq_zero zeros ones _).mpr position.isLt⟩
      left_inv := fun position => Subtype.ext (Fin.ext rfl)
      right_inv := fun position => Fin.ext rfl }
  exact (Fintype.card_congr fiberEquiv).trans (Fintype.card_fin zeros)

theorem canonicalWord_count_one (zeros ones : ℕ) :
    directionCount (canonicalWord zeros ones) 1 = ones := by
  let fiberEquiv : {position : Fin (zeros + ones) // canonicalWord zeros ones position = 1} ≃
      Fin ones :=
    { toFun := fun position =>
        ⟨position.val.val - zeros, by
          have lower := (canonicalWord_eq_one zeros ones position.val).mp position.property
          have upper := position.val.isLt
          omega⟩
      invFun := fun position =>
        ⟨⟨zeros + position.val, by omega⟩, (canonicalWord_eq_one zeros ones _).mpr (by
          change zeros ≤ zeros + position.val
          omega)⟩
      left_inv := fun position => by
        apply Subtype.ext
        apply Fin.ext
        have lower := (canonicalWord_eq_one zeros ones position.val).mp position.property
        change zeros + (position.val.val - zeros) = position.val.val
        omega
      right_inv := fun position => by
        apply Fin.ext
        change zeros + position.val - zeros = position.val
        omega }
  exact (Fintype.card_congr fiberEquiv).trans (Fintype.card_fin ones)

theorem sameCounts_canonical (zeros ones : ℕ) (word : Fin (zeros + ones) → Fin 2)
    (zeroCount : directionCount word 0 = zeros) (oneCount : directionCount word 1 = ones) :
    SameCounts word (canonicalWord zeros ones) := by
  intro direction
  fin_cases direction
  · exact zeroCount.trans (canonicalWord_count_zero zeros ones).symm
  · exact oneCount.trans (canonicalWord_count_one zeros ones).symm

end Grad.WeakTesting.Commutation
