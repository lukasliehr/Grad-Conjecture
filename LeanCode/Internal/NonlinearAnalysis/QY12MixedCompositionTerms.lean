import QY10MixedDirectional

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.MixedQuotientComposition

open Grad.CartesianState Grad.NonlinearQuotientBounds Grad.Constraints
open scoped BigOperators

/-- Literal finite seed, curvature and chart-state core, as a real vector space. -/
abbrev Input (parameters : PhaseParameters) := Seed.Parameters × JointState parameters

variable {parameters : PhaseParameters}

section Fibers

variable {order slots : ℕ}

def fiberTuple (assignment : Fin order → Fin slots) (slot : Fin slots)
    (directions : Fin order → Input parameters) :
    Fin (assignmentFiber assignment slot).card → Input parameters :=
  fun index => directions (fiberEnumeration assignment slot index)

variable (assignment : Fin order → Fin slots) (slot : Fin slots)

theorem fiberTuple_snoc_of_ne {other : Fin slots} (ne : other ≠ slot)
    (directions : Fin (order + 1) → Input parameters) :
    fiberTuple (Fin.snoc assignment slot) other directions =
      fiberTuple assignment other (fun position => directions position.castSucc) ∘
        Fin.cast (card_assignmentFiber_snoc_of_ne assignment slot ne) := by
  funext index
  unfold fiberTuple
  rw [fiberEnumeration_snoc_of_ne assignment slot ne]
  rfl

theorem fiberTuple_snoc_self (directions : Fin (order + 1) → Input parameters) :
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
    Fin.snoc (α := fun _ => Input parameters)
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

variable (family : (order : ℕ) → Input parameters →
  (Fin order → Input parameters) → QuotientState parameters)

/-- Transport of the inner family along an equality of orders. -/
theorem family_cast {count count' : ℕ} (equal : count = count') (base : Input parameters)
    (tuple : Fin count' → Input parameters) :
    family count base (tuple ∘ Fin.cast equal) = family count' base tuple := by
  subst equal
  rfl

variable {order slots : ℕ}

/-- The slot arguments of a term: the inner derivative of each block. -/
def termArguments (assignment : Fin order → Fin slots) (base : Input parameters)
    (directions : Fin order → Input parameters) : Fin slots → QuotientState parameters :=
  fun slot => family (assignmentFiber assignment slot).card base
    (fiberTuple assignment slot directions)

/-- The value of a term of the part `P`. -/
def termValue
    (P : MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters) (QuotientRows parameters))
    (assignment : Fin order → Fin slots) (base : Input parameters)
    (directions : Fin order → Input parameters) : QuotientRows parameters :=
  P (termArguments family assignment base directions)

/-- The composed `order`-th derivative of one homogeneous part: the sum over
all slot assignments of the directions. -/
def partComposedDerivative
    (P : MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters) (QuotientRows parameters))
    (order : ℕ) (base : Input parameters)
    (directions : Fin order → Input parameters) : QuotientRows parameters :=
  ∑ assignment : Fin order → Fin slots, termValue family P assignment base directions

theorem termArguments_snoc (assignment : Fin order → Fin slots) (slot : Fin slots)
    (base : Input parameters) (directions : Fin (order + 1) → Input parameters) :
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
    (base : Input parameters) (directions : Fin 0 → Input parameters) :
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
    (base : Input parameters) (directions : Fin (order + 1) → Input parameters) :
    partComposedDerivative family P (order + 1) base directions =
      ∑ assignment : Fin order → Fin slots, ∑ slot : Fin slots,
        termValue family P (Fin.snoc assignment slot) base directions := by
  unfold partComposedDerivative
  rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ => Fin slots))
    (fun pair => termValue family P (Fin.snoc pair.2 pair.1) base directions)
    (fun extended => termValue family P extended base directions) (fun _ => rfl),
    Fintype.sum_prod_type, Finset.sum_comm]

end Terms

end Grad.MixedQuotientComposition

