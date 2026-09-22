import QuotientStateSpace

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearQuotientBounds

/-!
Iterated directional derivatives of the diagonal restriction of a fixed
multilinear map, in exact finite form.  The `order`-th derivative of
`b ↦ W(b, …, b)` in the ordered directions `h₁, …, h_order` is the sum over
all injective placements of the directions into the slots of `W`, with the
base point in every remaining slot.  Everything in this module is finite
algebra; the one limit statement lives in `QuotientStateSpace`.
-/

section Placement

variable {V : Type*}

/-- All injective placements of `order` ordered directions into `slots` slots. -/
def slotInjections (order slots : ℕ) : Finset (Fin order → Fin slots) :=
  Finset.univ.filter Function.Injective

theorem mem_slotInjections {order slots : ℕ} {insertion : Fin order → Fin slots} :
    insertion ∈ slotInjections order slots ↔ Function.Injective insertion := by
  unfold slotInjections
  rw [Finset.mem_filter]
  exact ⟨fun paired => paired.2, fun injective => ⟨Finset.mem_univ _, injective⟩⟩

/-- The slots not hit by a placement. -/
def freeSlots {order slots : ℕ} (insertion : Fin order → Fin slots) : Finset (Fin slots) :=
  Finset.univ.filter (fun slot => ∀ position, insertion position ≠ slot)

theorem mem_freeSlots {order slots : ℕ} {insertion : Fin order → Fin slots} {slot : Fin slots} :
    slot ∈ freeSlots insertion ↔ ∀ position, insertion position ≠ slot := by
  unfold freeSlots
  rw [Finset.mem_filter]
  exact ⟨fun paired => paired.2, fun free => ⟨Finset.mem_univ _, free⟩⟩

theorem card_freeSlots_le {order slots : ℕ} (insertion : Fin order → Fin slots) :
    (freeSlots insertion).card ≤ slots := by
  have subset := Finset.card_le_card (Finset.subset_univ (freeSlots insertion))
  rwa [Finset.card_univ, Fintype.card_fin] at subset

/-- The argument tuple with direction `position` in slot `insertion position`
and the base state in every free slot. -/
def slotAssign {order slots : ℕ} (insertion : Fin order → Fin slots)
    (base : V) (directions : Fin order → V) : Fin slots → V :=
  fun slot =>
    if occupied : ∃ position, insertion position = slot then directions occupied.choose else base

theorem slotAssign_occupied {order slots : ℕ} {insertion : Fin order → Fin slots}
    (injective : Function.Injective insertion) (base : V) (directions : Fin order → V)
    (position : Fin order) :
    slotAssign insertion base directions (insertion position) = directions position := by
  have occupied : ∃ chosen, insertion chosen = insertion position := ⟨position, rfl⟩
  unfold slotAssign
  rw [dif_pos occupied]
  exact congrArg directions (injective occupied.choose_spec)

theorem slotAssign_free {order slots : ℕ} {insertion : Fin order → Fin slots}
    (base : V) (directions : Fin order → V) {slot : Fin slots}
    (free : ∀ position, insertion position ≠ slot) :
    slotAssign insertion base directions slot = base := by
  unfold slotAssign
  rw [dif_neg (fun occupied => occupied.elim (fun position hit => free position hit))]

theorem snoc_injective {order slots : ℕ} {insertion : Fin order → Fin slots} {slot : Fin slots}
    (injective : Function.Injective insertion) (free : ∀ position, insertion position ≠ slot) :
    Function.Injective (Fin.snoc insertion slot : Fin (order + 1) → Fin slots) := by
  intro left right equal
  rcases Fin.eq_castSucc_or_eq_last left with ⟨leftBase, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last right with ⟨rightBase, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc, Fin.snoc_castSucc] at equal
    exact congrArg Fin.castSucc (injective equal)
  · rw [Fin.snoc_castSucc, Fin.snoc_last] at equal
    exact absurd equal (free leftBase)
  · rw [Fin.snoc_last, Fin.snoc_castSucc] at equal
    exact absurd equal.symm (free rightBase)
  · rfl

theorem slotAssign_snoc {order slots : ℕ} {insertion : Fin order → Fin slots} {slot : Fin slots}
    (injective : Function.Injective insertion) (free : ∀ position, insertion position ≠ slot)
    (base direction : V) (directions : Fin order → V) :
    slotAssign (Fin.snoc insertion slot) base (Fin.snoc directions direction) =
      Function.update (slotAssign insertion base directions) slot direction := by
  have snocInjective := snoc_injective injective free
  funext target
  by_cases hit : target = slot
  · subst hit
    rw [Function.update_self]
    have occupiedForm := congrArg (slotAssign (Fin.snoc insertion target) base
      (Fin.snoc directions direction))
      (Fin.snoc_last (α := fun _ => Fin slots) target insertion).symm
    rw [occupiedForm, slotAssign_occupied snocInjective, Fin.snoc_last]
  · rw [Function.update_of_ne hit]
    by_cases occupied : ∃ position, insertion position = target
    · obtain ⟨position, rfl⟩ := occupied
      have castForm := congrArg (slotAssign (Fin.snoc insertion slot) base
        (Fin.snoc directions direction))
        (Fin.snoc_castSucc (α := fun _ => Fin slots) slot insertion position).symm
      rw [castForm, slotAssign_occupied snocInjective, Fin.snoc_castSucc,
        slotAssign_occupied injective]
    · push Not at occupied
      rw [slotAssign_free base directions occupied, slotAssign_free base _ ?_]
      intro extended
      rcases Fin.eq_castSucc_or_eq_last extended with ⟨position, rfl⟩ | rfl
      · rw [Fin.snoc_castSucc]
        exact occupied position
      · rw [Fin.snoc_last]
        exact fun equal => hit equal.symm


end Placement

variable {V E : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup E] [Module ℂ E]

/-- The exact `order`-th diagonal derivative of a fixed multilinear map. -/
def diagonalDerivative {slots : ℕ} (W : MultilinearMap ℂ (fun _ : Fin slots => V) E)
    (order : ℕ) (base : V) (directions : Fin order → V) : E :=
  ∑ insertion ∈ slotInjections order slots, W (slotAssign insertion base directions)

theorem diagonalDerivative_zero_of_lt {slots : ℕ}
    (W : MultilinearMap ℂ (fun _ : Fin slots => V) E) (order : ℕ)
    (base : V) (directions : Fin order → V) (exceeds : slots < order) :
    diagonalDerivative W order base directions = 0 := by
  unfold diagonalDerivative
  apply Finset.sum_eq_zero
  intro insertion membership
  have cardLe := Fintype.card_le_of_injective insertion (mem_slotInjections.mp membership)
  rw [Fintype.card_fin, Fintype.card_fin] at cardLe
  omega

theorem diagonalDerivative_zeroth {slots : ℕ}
    (W : MultilinearMap ℂ (fun _ : Fin slots => V) E) (base : V) (directions : Fin 0 → V) :
    diagonalDerivative W 0 base directions = W (fun _ => base) := by
  unfold diagonalDerivative
  have singleton : slotInjections 0 slots = {fun position => position.elim0} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    constructor
    · exact mem_slotInjections.mpr (fun position => position.elim0)
    · intro other _
      funext position
      exact position.elim0
  rw [singleton, Finset.sum_singleton]
  all_goals exact congrArg W (funext fun slot =>
    slotAssign_free base directions (fun position => position.elim0))

theorem diagonalDerivative_add {slots : ℕ}
    (first second : MultilinearMap ℂ (fun _ : Fin slots => V) E) (order : ℕ)
    (base : V) (directions : Fin order → V) :
    diagonalDerivative (first + second) order base directions =
      diagonalDerivative first order base directions +
        diagonalDerivative second order base directions := by
  unfold diagonalDerivative
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun insertion _ => rfl)

/-- The first-order coefficient of the shifted diagonal derivative is exactly
the next diagonal derivative, with the new direction in the final position. -/
theorem singleton_expansion_eq_succ {slots : ℕ}
    (W : MultilinearMap ℂ (fun _ : Fin slots => V) E) (order : ℕ)
    (base direction : V) (directions : Fin order → V) :
    (∑ insertion ∈ slotInjections order slots, ∑ slot ∈ freeSlots insertion,
      W (Function.update (slotAssign insertion base directions) slot direction)) =
      diagonalDerivative W (order + 1) base (Fin.snoc directions direction) := by
  unfold diagonalDerivative
  rw [Finset.sum_sigma']
  apply Finset.sum_nbij' (fun paired => Fin.snoc paired.1 paired.2)
    (fun extended => ⟨Fin.init extended, extended (Fin.last order)⟩)
  · intro paired membership
    rw [Finset.mem_sigma] at membership
    exact mem_slotInjections.mpr (snoc_injective (mem_slotInjections.mp membership.1)
      (fun position => mem_freeSlots.mp membership.2 position))
  · intro extended membership
    have injective := mem_slotInjections.mp membership
    rw [Finset.mem_sigma]
    constructor
    · apply mem_slotInjections.mpr
      intro left right equal
      exact Fin.castSucc_injective order (injective equal)
    · apply mem_freeSlots.mpr
      intro position equal
      have collapse : position.castSucc = Fin.last order := injective equal
      exact absurd collapse (ne_of_lt (Fin.castSucc_lt_last position))
  · intro paired membership
    apply Sigma.ext
    · exact Fin.init_snoc (α := fun _ => Fin slots) paired.2 paired.1
    · exact heq_of_eq (show Fin.snoc (α := fun _ => Fin slots) paired.1 paired.2
          (Fin.last order) = paired.2 from
        Fin.snoc_last (α := fun _ => Fin slots) paired.2 paired.1)
  · intro extended _
    exact Fin.snoc_init_self extended
  · intro paired membership
    rw [Finset.mem_sigma] at membership
    exact congrArg W (slotAssign_snoc (mem_slotInjections.mp membership.1)
      (fun position => mem_freeSlots.mp membership.2 position) base direction directions).symm

/-- Full literal polynomial expansion of a shifted diagonal derivative, with
the degree-zero and degree-one coefficients identified and every coefficient
above the number of slots equal to zero. -/
theorem diagonalDerivative_expansion {slots : ℕ}
    (W : MultilinearMap ℂ (fun _ : Fin slots => V) E) (order : ℕ)
    (base direction : V) (directions : Fin order → V) :
    ∃ coefficients : ℕ → E,
      coefficients 0 = diagonalDerivative W order base directions ∧
      coefficients 1 = diagonalDerivative W (order + 1) base (Fin.snoc directions direction) ∧
      (∀ power, slots < power → coefficients power = 0) ∧
      ∀ t : ℝ, diagonalDerivative W order (base + (t : ℂ) • direction) directions =
        ∑ power ∈ Finset.range (slots + 1), ((t : ℂ) ^ power) • coefficients power := by
  refine ⟨fun power => ∑ insertion ∈ slotInjections order slots,
    ∑ chosen ∈ Finset.powersetCard power (freeSlots insertion),
      W (chosen.piecewise (fun _ => direction) (slotAssign insertion base directions)),
    ?_, ?_, ?_, ?_⟩
  · unfold diagonalDerivative
    apply Finset.sum_congr rfl
    intro insertion _
    rw [Finset.powersetCard_zero, Finset.sum_singleton, Finset.piecewise_empty]
  · rw [← singleton_expansion_eq_succ W order base direction directions]
    apply Finset.sum_congr rfl
    intro insertion _
    rw [Finset.powersetCard_one, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro slot _
    exact congrArg W (Finset.piecewise_singleton _ _ _)
  · intro power exceeds
    apply Finset.sum_eq_zero
    intro insertion _
    rw [Finset.powersetCard_eq_empty.mpr (by
      have cardBound := card_freeSlots_le insertion
      omega), Finset.sum_empty]
  · intro t
    unfold diagonalDerivative
    have perInsertion : ∀ insertion ∈ slotInjections order slots,
        W (slotAssign insertion (base + (t : ℂ) • direction) directions) =
          ∑ power ∈ Finset.range (slots + 1), ((t : ℂ) ^ power) •
            ∑ chosen ∈ Finset.powersetCard power (freeSlots insertion),
              W (chosen.piecewise (fun _ => direction)
                (slotAssign insertion base directions)) := by
      intro insertion membership
      have injective := mem_slotInjections.mp membership
      have shiftedAssign : slotAssign insertion (base + (t : ℂ) • direction) directions =
          (freeSlots insertion).piecewise
            ((fun _ => (t : ℂ) • direction) + slotAssign insertion base directions)
            (slotAssign insertion base directions) := by
        funext slot
        by_cases free : slot ∈ freeSlots insertion
        · rw [Finset.piecewise_eq_of_mem _ _ _ free, Pi.add_apply,
            slotAssign_free base directions (mem_freeSlots.mp free),
            slotAssign_free (base + (t : ℂ) • direction) directions (mem_freeSlots.mp free)]
          exact add_comm _ _
        · have occupied : ∃ position, insertion position = slot := by
            by_contra vacant
            push Not at vacant
            exact free (mem_freeSlots.mpr vacant)
          obtain ⟨position, rfl⟩ := occupied
          rw [Finset.piecewise_eq_of_notMem _ _ _ free,
            slotAssign_occupied injective, slotAssign_occupied injective]
      have perSubset : ∀ chosen ∈ (freeSlots insertion).powerset,
          W (chosen.piecewise (fun _ => (t : ℂ) • direction)
            (slotAssign insertion base directions)) =
          ((t : ℂ) ^ chosen.card) • W (chosen.piecewise (fun _ => direction)
            (slotAssign insertion base directions)) := by
        intro chosen _
        have pointwise : chosen.piecewise (fun _ => (t : ℂ) • direction)
            (slotAssign insertion base directions) =
            fun slot => (chosen.piecewise (fun _ => (t : ℂ)) (fun _ => (1 : ℂ)) slot) •
              (chosen.piecewise (fun _ => direction)
                (slotAssign insertion base directions) slot) := by
          funext slot
          by_cases inside : slot ∈ chosen
          · rw [Finset.piecewise_eq_of_mem _ _ _ inside,
              Finset.piecewise_eq_of_mem _ _ _ inside,
              Finset.piecewise_eq_of_mem _ _ _ inside]
          · rw [Finset.piecewise_eq_of_notMem _ _ _ inside,
              Finset.piecewise_eq_of_notMem _ _ _ inside,
              Finset.piecewise_eq_of_notMem _ _ _ inside, one_smul]
        rw [pointwise, W.map_smul_univ]
        congr 1
        rw [Finset.prod_piecewise, Finset.univ_inter, Finset.prod_const,
          Finset.prod_const_one, mul_one]
      have padded : Finset.range ((freeSlots insertion).card + 1) ⊆
          Finset.range (slots + 1) := by
        intro member membership
        rw [Finset.mem_range] at membership ⊢
        have cardBound := card_freeSlots_le insertion
        omega
      have vanishOutside : ∀ power ∈ Finset.range (slots + 1),
          power ∉ Finset.range ((freeSlots insertion).card + 1) →
          (∑ chosen ∈ Finset.powersetCard power (freeSlots insertion),
            ((t : ℂ) ^ chosen.card) • W (chosen.piecewise (fun _ => direction)
              (slotAssign insertion base directions))) = 0 := by
        intro power _ outside
        have exceeds : (freeSlots insertion).card < power := by
          rw [Finset.mem_range, not_lt] at outside
          omega
        rw [Finset.powersetCard_eq_empty.mpr exceeds, Finset.sum_empty]
      rw [shiftedAssign, W.map_piecewise_add, Finset.sum_congr rfl perSubset,
        Finset.sum_powerset, Finset.sum_subset padded vanishOutside]
      apply Finset.sum_congr rfl
      intro power _
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro chosen chosenMembership
      rw [(Finset.mem_powersetCard.mp chosenMembership).2]
    rw [Finset.sum_congr rfl perInsertion, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro power _
    exact (Finset.smul_sum).symm

end Grad.NonlinearQuotientBounds
