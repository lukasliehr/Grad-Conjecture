import OM1Interface

noncomputable section

open scoped BigOperators

namespace Grad.OrderedMultiplicity

open Grad.GenericCarriers

universe valueUniverse

def wordSubsetEquiv (rank : ℕ) : (Fin rank → Fin 2) ≃ Finset (Fin rank) where
  toFun := zeroPositions
  invFun subset := fun position => if position ∈ subset then 0 else 1
  left_inv word := by
    funext position
    simp only [zeroPositions, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with zero
    · exact zero.symm
    · omega
  right_inv subset := by
    ext position
    simp [zeroPositions]

def fiberSubsetEquiv (rank : ℕ) (zeros : Fin (rank + 1)) :
    {word : Fin rank → Fin 2 // countZeros word = zeros} ≃
      {subset : Finset (Fin rank) // subset ∈ Finset.univ.powersetCard zeros.val} :=
  (wordSubsetEquiv rank).subtypeEquiv fun word => by
    change countZeros word = zeros ↔ zeroPositions word ∈ Finset.univ.powersetCard zeros.val
    rw [Finset.mem_powersetCard]
    simp only [Finset.subset_univ, true_and]
    exact Fin.ext_iff

theorem fiber_card (rank : ℕ) (zeros : Fin (rank + 1)) :
    Fintype.card {word : Fin rank → Fin 2 // countZeros word = zeros} = rank.choose zeros.val := by
  rw [Fintype.card_congr (fiberSubsetEquiv rank zeros)]
  simp only [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

def initialSegmentEquiv (rank : ℕ) (zeros : Fin (rank + 1)) :
    {position : Fin rank // position.val < zeros.val} ≃ Fin zeros.val where
  toFun position := ⟨position.val.val, position.property⟩
  invFun position := ⟨⟨position.val, lt_of_lt_of_le position.isLt (Nat.le_of_lt_succ zeros.isLt)⟩,
    position.isLt⟩
  left_inv position := by apply Subtype.ext; rfl
  right_inv position := by apply Fin.ext; rfl

theorem canonical_count (rank : ℕ) (zeros : Fin (rank + 1)) :
    countZeros (canonicalWord rank zeros) = zeros := by
  apply Fin.ext
  change (zeroPositions (canonicalWord rank zeros)).card = zeros.val
  calc
    _ = Fintype.card {position : Fin rank // position.val < zeros.val} := by
      simp [zeroPositions, canonicalWord, Fintype.card_subtype]
    _ = Fintype.card (Fin zeros.val) := Fintype.card_congr (initialSegmentEquiv rank zeros)
    _ = zeros.val := Fintype.card_fin zeros.val

theorem multiIndexEquiv_apply (rank : ℕ) (zeros : Fin (rank + 1)) :
    (multiIndexEquiv rank zeros).val = (zeros.val, rank - zeros.val) := rfl

theorem one_count (rank : ℕ) (word : Fin rank → Fin 2) :
    Fintype.card {position : Fin rank // word position = 1} = rank - (countZeros word).val := by
  rw [Fintype.card_subtype]
  have complement : Finset.univ.filter (fun position => ¬ word position = 0) =
      Finset.univ.filter (fun position => word position = 1) := by
    ext position
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have partition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin rank))) (fun position => word position = 0)
  rw [complement, Finset.card_univ, Fintype.card_fin] at partition
  change (Finset.univ.filter (fun position => word position = 1)).card =
    rank - (Finset.univ.filter (fun position => word position = 0)).card
  omega

theorem combinatorial : CombinatorialGoal :=
  ⟨fiber_card, canonical_count, multiIndexEquiv_apply, one_count⟩

theorem choose_bounds (rank : ℕ) (zeros : Fin (rank + 1)) :
    1 ≤ rank.choose zeros.val ∧ rank.choose zeros.val ≤ rank.factorial := by
  constructor
  · exact Nat.succ_le_of_lt (Nat.choose_pos (Nat.le_of_lt_succ zeros.isLt))
  · rw [Nat.choose_eq_factorial_div_factorial (Nat.le_of_lt_succ zeros.isLt)]
    exact Nat.div_le_self _ _

variable {Value : Type valueUniverse} [NormedAddCommGroup Value]

theorem orderedTensor_apply (rank : ℕ) (family : Fin (rank + 1) → Value)
    (word : Fin rank → Fin 2) : orderedTensor rank family word = family (countZeros word) := rfl

theorem multiTensor_apply (rank : ℕ) (family : Fin (rank + 1) → Value)
    (zeros : Fin (rank + 1)) : multiTensor rank family zeros = family zeros := rfl

theorem multiplicity_formula (rank : ℕ) (family : Fin (rank + 1) → Value) :
    ∑ word : Fin rank → Fin 2, ‖family (countZeros word)‖ ^ 2 =
      ∑ zeros : Fin (rank + 1), (rank.choose zeros.val : ℝ) * ‖family zeros‖ ^ 2 := by
  rw [← Fintype.sum_fiberwise' (@countZeros rank) (fun zeros => ‖family zeros‖ ^ 2)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, fiber_card]

theorem multiIndex_formula (rank : ℕ) (family : TopMultiIndex rank → Value) :
    ∑ word : Fin rank → Fin 2, ‖family (multiIndexEquiv rank (countZeros word))‖ ^ 2 =
      ∑ beta : TopMultiIndex rank, (rank.choose beta.val.1 : ℝ) * ‖family beta‖ ^ 2 := by
  calc
    _ = ∑ zeros : Fin (rank + 1), (rank.choose zeros.val : ℝ) *
        ‖family (multiIndexEquiv rank zeros)‖ ^ 2 :=
      multiplicity_formula rank (fun zeros => family (multiIndexEquiv rank zeros))
    _ = _ := Fintype.sum_equiv (multiIndexEquiv rank) _ _ (fun _ => rfl)

theorem topMulti_sq (rank : ℕ) (family : Fin (rank + 1) → Value) :
    topMulti rank family ^ 2 = ∑ zeros : Fin (rank + 1), ‖family zeros‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ (multiTensor rank family)

theorem topOrdered_sq (rank : ℕ) (family : Fin (rank + 1) → Value) :
    topOrdered rank family ^ 2 = ∑ word : Fin rank → Fin 2, ‖family (countZeros word)‖ ^ 2 :=
  tensor_norm_sq rank (orderedTensor rank family)

theorem norm_comparison (rank : ℕ) (family : Fin (rank + 1) → Value) :
    topMulti rank family ≤ topOrdered rank family ∧
    topOrdered rank family ≤ Real.sqrt (rank.factorial : ℝ) * topMulti rank family := by
  constructor
  · apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change topMulti rank family ^ 2 ≤ topOrdered rank family ^ 2
    rw [topMulti_sq, topOrdered_sq, multiplicity_formula]
    apply Finset.sum_le_sum
    intro zeros _
    have lower : (1 : ℝ) ≤ (rank.choose zeros.val : ℝ) := by
      exact_mod_cast (choose_bounds rank zeros).1
    simpa only [one_mul] using mul_le_mul_of_nonneg_right lower (sq_nonneg ‖family zeros‖)
  · apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    change topOrdered rank family ^ 2 ≤ (Real.sqrt (rank.factorial : ℝ) * topMulti rank family) ^ 2
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), topOrdered_sq, multiplicity_formula,
      topMulti_sq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro zeros _
    have upper : (rank.choose zeros.val : ℝ) ≤ (rank.factorial : ℝ) := by
      exact_mod_cast (choose_bounds rank zeros).2
    exact mul_le_mul_of_nonneg_right upper (sq_nonneg ‖family zeros‖)

theorem topMulti_zero (family : Fin 1 → Value) : topMulti 0 family = ‖family 0‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change topMulti 0 family ^ 2 = ‖family 0‖ ^ 2
  rw [topMulti_sq]
  simp

theorem topOrdered_zero (family : Fin 1 → Value) : topOrdered 0 family = ‖family 0‖ := by
  have comparison := norm_comparison 0 family
  simp only [Nat.factorial_zero, Nat.cast_one, Real.sqrt_one, one_mul, topMulti_zero] at comparison
  exact le_antisymm comparison.2 comparison.1

theorem multiplicity : MultiplicityGoal.{valueUniverse} := fun _ _ _ => multiplicity_formula

theorem multiIndex : MultiIndexGoal.{valueUniverse} := fun _ _ _ => multiIndex_formula

theorem normComparison : NormGoal.{valueUniverse} := fun _ _ _ rank family =>
  ⟨topMulti_sq rank family, topOrdered_sq rank family, norm_comparison rank family⟩

theorem zero : ZeroGoal.{valueUniverse} := fun _ _ _ family =>
  ⟨topMulti_zero family, topOrdered_zero family⟩

theorem algebraBlock : AlgebraBlockGoal.{valueUniverse} :=
  ⟨combinatorial, multiplicity, multiIndex, normComparison, zero⟩

end Grad.OrderedMultiplicity
