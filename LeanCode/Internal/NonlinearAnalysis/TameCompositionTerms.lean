import TameCompositionCalculus

noncomputable section

set_option maxHeartbeats 1600000

open Filter
open scoped BigOperators Topology

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.Constraints

/-! # Set-partition terms of the composed derivative

The `k`-th derivative of a homogeneous part `P` composed with an inner map is
indexed by the slot assignments `σ : Fin k → Fin d`: every slot receives the
block of directions assigned to it (its fiber, enumerated increasingly), as
the inner derivative of that block's order. Adding the newest direction to a
term means assigning it to one slot; this is the exact recursion behind the
finite set-partition chain rule. -/

variable {parameters : PhaseParameters}

section Fibers

variable {order slots : ℕ}

/-- The fiber of a slot assignment over a slot. -/
def assignmentFiber (assignment : Fin order → Fin slots) (slot : Fin slots) : Finset (Fin order) :=
  Finset.univ.filter (fun position => assignment position = slot)

theorem mem_assignmentFiber {assignment : Fin order → Fin slots} {slot : Fin slots}
    {position : Fin order} :
    position ∈ assignmentFiber assignment slot ↔ assignment position = slot := by
  unfold assignmentFiber
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The increasing enumeration of a fiber. -/
def fiberEnumeration (assignment : Fin order → Fin slots) (slot : Fin slots) :
    Fin (assignmentFiber assignment slot).card → Fin order :=
  (assignmentFiber assignment slot).orderEmbOfFin rfl

theorem fiberEnumeration_mem (assignment : Fin order → Fin slots) (slot : Fin slots)
    (index : Fin (assignmentFiber assignment slot).card) :
    assignment (fiberEnumeration assignment slot index) = slot :=
  mem_assignmentFiber.mp (Finset.orderEmbOfFin_mem _ rfl index)

theorem fiberEnumeration_strictMono (assignment : Fin order → Fin slots) (slot : Fin slots) :
    StrictMono (fiberEnumeration assignment slot) :=
  ((assignmentFiber assignment slot).orderEmbOfFin rfl).strictMono

/-- The direction tuple of a slot: the directions of its fiber in order. -/
def fiberTuple (assignment : Fin order → Fin slots) (slot : Fin slots)
    (directions : Fin order → JointState parameters) :
    Fin (assignmentFiber assignment slot).card → JointState parameters :=
  fun index => directions (fiberEnumeration assignment slot index)

/-- The castSucc embedding, definitionally `Fin.castSucc`. -/
def castSuccEmbedding (order : ℕ) : Fin order ↪ Fin (order + 1) :=
  ⟨Fin.castSucc, Fin.castSucc_injective order⟩

variable (assignment : Fin order → Fin slots) (slot : Fin slots)

theorem assignmentFiber_snoc_of_ne {other : Fin slots} (ne : other ≠ slot) :
    assignmentFiber (Fin.snoc assignment slot) other =
      (assignmentFiber assignment other).map (castSuccEmbedding order) := by
  ext position
  rw [mem_assignmentFiber, Finset.mem_map]
  constructor
  · intro value
    rcases Fin.eq_castSucc_or_eq_last position with ⟨q, rfl⟩ | rfl
    · rw [Fin.snoc_castSucc] at value
      exact ⟨q, mem_assignmentFiber.mpr value, rfl⟩
    · rw [Fin.snoc_last] at value
      exact absurd value.symm ne
  · rintro ⟨q, mem, rfl⟩
    show Fin.snoc (α := fun _ => Fin slots) assignment slot (Fin.castSucc q) = other
    rw [Fin.snoc_castSucc]
    exact mem_assignmentFiber.mp mem

theorem assignmentFiber_snoc_self :
    assignmentFiber (Fin.snoc assignment slot) slot =
      insert (Fin.last order) ((assignmentFiber assignment slot).map (castSuccEmbedding order)) := by
  ext position
  rw [mem_assignmentFiber, Finset.mem_insert, Finset.mem_map]
  constructor
  · intro value
    rcases Fin.eq_castSucc_or_eq_last position with ⟨q, rfl⟩ | rfl
    · right
      rw [Fin.snoc_castSucc] at value
      exact ⟨q, mem_assignmentFiber.mpr value, rfl⟩
    · left
      rfl
  · rintro (rfl | ⟨q, mem, rfl⟩)
    · exact Fin.snoc_last (α := fun _ => Fin slots) slot assignment
    · show Fin.snoc (α := fun _ => Fin slots) assignment slot (Fin.castSucc q) = slot
      rw [Fin.snoc_castSucc]
      exact mem_assignmentFiber.mp mem

theorem card_assignmentFiber_snoc_of_ne {other : Fin slots} (ne : other ≠ slot) :
    (assignmentFiber (Fin.snoc assignment slot) other).card =
      (assignmentFiber assignment other).card := by
  rw [assignmentFiber_snoc_of_ne assignment slot ne, Finset.card_map]

theorem card_assignmentFiber_snoc_self :
    (assignmentFiber (Fin.snoc assignment slot) slot).card =
      (assignmentFiber assignment slot).card + 1 := by
  rw [assignmentFiber_snoc_self, Finset.card_insert_of_notMem, Finset.card_map]
  intro mem
  obtain ⟨q, _, eq⟩ := Finset.mem_map.mp mem
  exact absurd eq (ne_of_lt (Fin.castSucc_lt_last q))

theorem fiberEnumeration_snoc_of_ne {other : Fin slots} (ne : other ≠ slot) :
    fiberEnumeration (Fin.snoc assignment slot) other =
      Fin.castSucc ∘ fiberEnumeration assignment other ∘
        Fin.cast (card_assignmentFiber_snoc_of_ne assignment slot ne) := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro index
    rw [mem_assignmentFiber]
    show Fin.snoc (α := fun _ => Fin slots) assignment slot
      (Fin.castSucc (fiberEnumeration assignment other
        (Fin.cast (card_assignmentFiber_snoc_of_ne assignment slot ne) index))) = other
    rw [Fin.snoc_castSucc]
    exact fiberEnumeration_mem assignment other _
  · exact Fin.strictMono_castSucc.comp
      ((fiberEnumeration_strictMono assignment other).comp (Fin.cast_strictMono _))

/-- Appending the last index to an increasing enumeration stays increasing. -/
theorem snoc_castSucc_strictMono {count : ℕ} (enumeration : Fin count → Fin order)
    (mono : StrictMono enumeration) :
    StrictMono (Fin.snoc (Fin.castSucc ∘ enumeration) (Fin.last order) :
      Fin (count + 1) → Fin (order + 1)) := by
  intro a b lt
  rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact Fin.castSucc_lt_castSucc_iff.mpr (mono (Fin.castSucc_lt_castSucc_iff.mp lt))
    · exact absurd lt (not_lt.mpr (Fin.le_last _))
  · rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl
    · rw [Fin.snoc_castSucc, Fin.snoc_last]
      exact Fin.castSucc_lt_last _
    · exact absurd lt (lt_irrefl _)

theorem fiberEnumeration_snoc_self :
    fiberEnumeration (Fin.snoc assignment slot) slot =
      Fin.snoc (Fin.castSucc ∘ fiberEnumeration assignment slot) (Fin.last order) ∘
        Fin.cast (card_assignmentFiber_snoc_self assignment slot) := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro index
    rw [mem_assignmentFiber]
    show Fin.snoc (α := fun _ => Fin slots) assignment slot
      (Fin.snoc (α := fun _ => Fin (order + 1)) (Fin.castSucc ∘ fiberEnumeration assignment slot)
        (Fin.last order) (Fin.cast (card_assignmentFiber_snoc_self assignment slot) index)) = slot
    rcases Fin.eq_castSucc_or_eq_last
      (Fin.cast (card_assignmentFiber_snoc_self assignment slot) index) with ⟨q, eq⟩ | eq
    · rw [eq, Fin.snoc_castSucc]
      show Fin.snoc (α := fun _ => Fin slots) assignment slot
        (Fin.castSucc (fiberEnumeration assignment slot q)) = slot
      rw [Fin.snoc_castSucc]
      exact fiberEnumeration_mem assignment slot q
    · rw [eq, Fin.snoc_last, Fin.snoc_last]
  · exact (snoc_castSucc_strictMono (fiberEnumeration assignment slot)
      (fiberEnumeration_strictMono assignment slot)).comp (Fin.cast_strictMono _)

theorem fiberTuple_snoc_of_ne {other : Fin slots} (ne : other ≠ slot)
    (directions : Fin (order + 1) → JointState parameters) :
    fiberTuple (Fin.snoc assignment slot) other directions =
      fiberTuple assignment other (fun position => directions position.castSucc) ∘
        Fin.cast (card_assignmentFiber_snoc_of_ne assignment slot ne) := by
  funext index
  unfold fiberTuple
  rw [fiberEnumeration_snoc_of_ne assignment slot ne]
  rfl

theorem fiberTuple_snoc_self (directions : Fin (order + 1) → JointState parameters) :
    fiberTuple (Fin.snoc assignment slot) slot directions =
      Fin.snoc (fiberTuple assignment slot (fun position => directions position.castSucc))
        (directions (Fin.last order)) ∘
        Fin.cast (card_assignmentFiber_snoc_self assignment slot) := by
  funext index
  unfold fiberTuple
  rw [fiberEnumeration_snoc_self assignment slot]
  show directions (Fin.snoc (α := fun _ => Fin (order + 1))
      (Fin.castSucc ∘ fiberEnumeration assignment slot) (Fin.last order)
      (Fin.cast (card_assignmentFiber_snoc_self assignment slot) index)) =
    Fin.snoc (α := fun _ => JointState parameters)
      (fun q => directions (fiberEnumeration assignment slot q).castSucc)
      (directions (Fin.last order))
      (Fin.cast (card_assignmentFiber_snoc_self assignment slot) index)
  rcases Fin.eq_castSucc_or_eq_last
    (Fin.cast (card_assignmentFiber_snoc_self assignment slot) index) with ⟨q, eq⟩ | eq
  · rw [eq, Fin.snoc_castSucc, Fin.snoc_castSucc]
    rfl
  · rw [eq, Fin.snoc_last, Fin.snoc_last]

end Fibers

/-! ### Term evaluation and the composed derivative of one part -/

section Terms

variable (family : (order : ℕ) → JointState parameters →
  (Fin order → JointState parameters) → QuotientState parameters)

/-- Transport of the inner family along an equality of orders. -/
theorem family_cast {count count' : ℕ} (equal : count = count') (base : JointState parameters)
    (tuple : Fin count' → JointState parameters) :
    family count base (tuple ∘ Fin.cast equal) = family count' base tuple := by
  subst equal
  rfl

variable {order slots : ℕ}

/-- The slot arguments of a term: the inner derivative of each block. -/
def termArguments (assignment : Fin order → Fin slots) (base : JointState parameters)
    (directions : Fin order → JointState parameters) : Fin slots → QuotientState parameters :=
  fun slot => family (assignmentFiber assignment slot).card base
    (fiberTuple assignment slot directions)

/-- The value of a term of the part `P`. -/
def termValue
    (P : MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters) (QuotientRows parameters))
    (assignment : Fin order → Fin slots) (base : JointState parameters)
    (directions : Fin order → JointState parameters) : QuotientRows parameters :=
  P (termArguments family assignment base directions)

/-- The composed `order`-th derivative of one homogeneous part: the sum over
all slot assignments of the directions. -/
def partComposedDerivative
    (P : MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters) (QuotientRows parameters))
    (order : ℕ) (base : JointState parameters)
    (directions : Fin order → JointState parameters) : QuotientRows parameters :=
  ∑ assignment : Fin order → Fin slots, termValue family P assignment base directions

theorem termArguments_snoc (assignment : Fin order → Fin slots) (slot : Fin slots)
    (base : JointState parameters) (directions : Fin (order + 1) → JointState parameters) :
    termArguments family (Fin.snoc assignment slot) base directions =
      Function.update
        (termArguments family assignment base (fun position => directions position.castSucc)) slot
        (family ((assignmentFiber assignment slot).card + 1) base
          (Fin.snoc (fiberTuple assignment slot (fun position => directions position.castSucc))
            (directions (Fin.last order)))) := by
  funext other
  by_cases equal : other = slot
  · subst equal
    rw [Function.update_self]
    unfold termArguments
    rw [fiberTuple_snoc_self, family_cast family]
  · rw [Function.update_of_ne equal]
    unfold termArguments
    rw [fiberTuple_snoc_of_ne assignment slot equal, family_cast family]

theorem partComposedDerivative_zeroth
    (P : MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters) (QuotientRows parameters))
    (base : JointState parameters) (directions : Fin 0 → JointState parameters) :
    partComposedDerivative family P 0 base directions =
      P (fun _ => family 0 base (fun position => position.elim0)) := by
  unfold partComposedDerivative
  rw [Fintype.sum_unique]
  unfold termValue
  congr 1
  funext slot
  unfold termArguments
  have card_zero : (assignmentFiber (default : Fin 0 → Fin slots) slot).card = 0 :=
    Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun position _ => position.elim0)
  rw [show fiberTuple (default : Fin 0 → Fin slots) slot directions =
      (fun position : Fin 0 => position.elim0) ∘ Fin.cast card_zero from
        funext fun index => (Fin.cast card_zero index).elim0, family_cast family]

/-- The recursion: the assignments of `order + 1` directions are the
assignments of the first `order` directions with the newest direction placed
in one slot. -/
theorem partComposedDerivative_succ
    (P : MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters) (QuotientRows parameters))
    (base : JointState parameters) (directions : Fin (order + 1) → JointState parameters) :
    partComposedDerivative family P (order + 1) base directions =
      ∑ assignment : Fin order → Fin slots, ∑ slot : Fin slots,
        termValue family P (Fin.snoc assignment slot) base directions := by
  unfold partComposedDerivative
  rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ => Fin slots))
    (fun pair => termValue family P (Fin.snoc pair.2 pair.1) base directions)
    (fun extended => termValue family P extended base directions) (fun _ => rfl),
    Fintype.sum_prod_type, Finset.sum_comm]

end Terms

end Grad.NonlinearQuotientBounds
