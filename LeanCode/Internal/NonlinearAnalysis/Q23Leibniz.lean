import Q23SeedTransferDerivatives
import TameCompositionTerms

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 2400000

open Set
open scoped BigOperators ContDiff

namespace Grad.NonlinearQuotientBounds

/-! A direction-sensitive all-orders Leibniz formula.  Mathlib supplies the
corresponding operator-norm estimate, but the exact allocation identity is
needed here to show that derivatives of the completed seed operators still
carry the accepted all-grade smooth core to itself. -/

/-- The increasing tuple of directions in one fiber of a slot assignment. -/
def q23FiberTuple {Direction : Type*} {order slots : ℕ}
    (assignment : Fin order → Fin slots) (slot : Fin slots)
    (directions : Fin order → Direction) :
    Fin (assignmentFiber assignment slot).card → Direction :=
  fun index => directions (fiberEnumeration assignment slot index)

/-- The positive-index embedding used when a new direction is prepended. -/
def q23SuccEmbedding (order : ℕ) : Fin order ↪ Fin (order + 1) :=
  ⟨Fin.succ, Fin.succ_injective order⟩

theorem assignmentFiber_cons_of_ne {order slots : ℕ}
    (assignment : Fin order → Fin slots) (slot other : Fin slots)
    (ne : other ≠ slot) :
    assignmentFiber (Fin.cons slot assignment) other =
      (assignmentFiber assignment other).map (q23SuccEmbedding order) := by
  ext position
  rw [mem_assignmentFiber, Finset.mem_map]
  constructor
  · intro value
    rcases Fin.eq_zero_or_eq_succ position with rfl | ⟨q, rfl⟩
    · rw [Fin.cons_zero] at value
      exact absurd value.symm ne
    · rw [Fin.cons_succ] at value
      exact ⟨q, mem_assignmentFiber.mpr value, rfl⟩
  · rintro ⟨q, mem, rfl⟩
    change (Fin.cons (α := fun _ : Fin (order + 1) => Fin slots)
      slot assignment) q.succ = other
    simpa only [Fin.cons_succ] using
      (mem_assignmentFiber.mp mem)

theorem assignmentFiber_cons_self {order slots : ℕ}
    (assignment : Fin order → Fin slots) (slot : Fin slots) :
    assignmentFiber (Fin.cons slot assignment) slot =
      insert 0 ((assignmentFiber assignment slot).map (q23SuccEmbedding order)) := by
  ext position
  rw [mem_assignmentFiber, Finset.mem_insert, Finset.mem_map]
  constructor
  · intro value
    rcases Fin.eq_zero_or_eq_succ position with rfl | ⟨q, rfl⟩
    · exact Or.inl rfl
    · rw [Fin.cons_succ] at value
      exact Or.inr ⟨q, mem_assignmentFiber.mpr value, rfl⟩
  · rintro (rfl | ⟨q, mem, rfl⟩)
    · rfl
    · change (Fin.cons (α := fun _ : Fin (order + 1) => Fin slots)
        slot assignment) q.succ = slot
      simpa only [Fin.cons_succ] using
        (mem_assignmentFiber.mp mem)

theorem card_assignmentFiber_cons_of_ne {order slots : ℕ}
    (assignment : Fin order → Fin slots) (slot other : Fin slots)
    (ne : other ≠ slot) :
    (assignmentFiber (Fin.cons slot assignment) other).card =
      (assignmentFiber assignment other).card := by
  rw [assignmentFiber_cons_of_ne assignment slot other ne, Finset.card_map]

theorem card_assignmentFiber_cons_self {order slots : ℕ}
    (assignment : Fin order → Fin slots) (slot : Fin slots) :
    (assignmentFiber (Fin.cons slot assignment) slot).card =
      (assignmentFiber assignment slot).card + 1 := by
  rw [assignmentFiber_cons_self assignment slot, Finset.card_insert_of_notMem,
    Finset.card_map]
  intro mem
  obtain ⟨q, _, eq⟩ := Finset.mem_map.mp mem
  change q.succ = 0 at eq
  exact Fin.succ_ne_zero q eq

theorem fiberEnumeration_cons_of_ne {order slots : ℕ}
    (assignment : Fin order → Fin slots) (slot other : Fin slots)
    (ne : other ≠ slot) :
    fiberEnumeration (Fin.cons slot assignment) other =
      Fin.succ ∘ fiberEnumeration assignment other ∘
        Fin.cast (card_assignmentFiber_cons_of_ne assignment slot other ne) := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro index
    rw [mem_assignmentFiber]
    change (Fin.cons (α := fun _ : Fin (order + 1) => Fin slots)
      slot assignment)
        (fiberEnumeration assignment other
          (Fin.cast (card_assignmentFiber_cons_of_ne assignment slot other ne) index)).succ = other
    simpa only [Fin.cons_succ] using
      (fiberEnumeration_mem assignment other
        (Fin.cast (card_assignmentFiber_cons_of_ne assignment slot other ne) index))
  · exact Fin.strictMono_succ.comp
      ((fiberEnumeration_strictMono assignment other).comp (Fin.cast_strictMono _))

theorem q23_cons_zero_succ_strictMono {count order : ℕ}
    (enumeration : Fin count → Fin order) (mono : StrictMono enumeration) :
    StrictMono (Fin.cons 0 (Fin.succ ∘ enumeration) :
      Fin (count + 1) → Fin (order + 1)) := by
  intro a b lt
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a', rfl⟩
  · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
    · exact absurd lt (lt_irrefl _)
    · rw [Fin.cons_zero, Fin.cons_succ]
      exact Fin.pos_iff_ne_zero.mpr (Fin.succ_ne_zero _)
  · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
    · exact absurd lt (not_lt.mpr (Fin.zero_le _))
    · rw [Fin.cons_succ, Fin.cons_succ]
      exact Fin.succ_lt_succ_iff.mpr (mono (Fin.succ_lt_succ_iff.mp lt))

theorem fiberEnumeration_cons_self {order slots : ℕ}
    (assignment : Fin order → Fin slots) (slot : Fin slots) :
    fiberEnumeration (Fin.cons slot assignment) slot =
      Fin.cons 0 (Fin.succ ∘ fiberEnumeration assignment slot) ∘
        Fin.cast (card_assignmentFiber_cons_self assignment slot) := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro index
    rw [mem_assignmentFiber]
    simp only [Function.comp_apply]
    rcases Fin.eq_zero_or_eq_succ
      (Fin.cast (card_assignmentFiber_cons_self assignment slot) index) with eq | ⟨q, eq⟩
    · rw [eq, Fin.cons_zero, Fin.cons_zero]
    · rw [eq, Fin.cons_succ]
      change (Fin.cons (α := fun _ : Fin (order + 1) => Fin slots)
        slot assignment) (fiberEnumeration assignment slot q).succ = slot
      rw [Fin.cons_succ]
      exact fiberEnumeration_mem assignment slot q
  · exact (q23_cons_zero_succ_strictMono (fiberEnumeration assignment slot)
      (fiberEnumeration_strictMono assignment slot)).comp (Fin.cast_strictMono _)

theorem q23FiberTuple_cons_of_ne {Direction : Type*} {order slots : ℕ}
    (assignment : Fin order → Fin slots) (slot other : Fin slots)
    (ne : other ≠ slot) (directions : Fin (order + 1) → Direction) :
    q23FiberTuple (Fin.cons slot assignment) other directions =
      q23FiberTuple assignment other (Fin.tail directions) ∘
        Fin.cast (card_assignmentFiber_cons_of_ne assignment slot other ne) := by
  funext index
  unfold q23FiberTuple
  rw [fiberEnumeration_cons_of_ne assignment slot other ne]
  simp only [Function.comp_apply, Fin.tail_def]

theorem q23FiberTuple_cons_self {Direction : Type*} {order slots : ℕ}
    (assignment : Fin order → Fin slots) (slot : Fin slots)
    (directions : Fin (order + 1) → Direction) :
    q23FiberTuple (Fin.cons slot assignment) slot directions =
      Fin.cons (directions 0)
        (q23FiberTuple assignment slot (Fin.tail directions)) ∘
        Fin.cast (card_assignmentFiber_cons_self assignment slot) := by
  funext index
  unfold q23FiberTuple
  rw [fiberEnumeration_cons_self assignment slot]
  simp only [Function.comp_apply]
  rcases Fin.eq_zero_or_eq_succ
    (Fin.cast (card_assignmentFiber_cons_self assignment slot) index) with eq | ⟨q, eq⟩
  · rw [eq, Fin.cons_zero, Fin.cons_zero]
  · rw [eq, Fin.cons_succ, Fin.cons_succ]
    rfl

section Bilinear

variable {𝕜 D E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem q23IteratedFDerivWithin_cast {count count' : ℕ}
    (equal : count = count') (f : D → E) (domain : Set D) (point : D)
    (directions : Fin count' → D) :
    iteratedFDerivWithin 𝕜 count f domain point (directions ∘ Fin.cast equal) =
      iteratedFDerivWithin 𝕜 count' f domain point directions := by
  subst equal
  rfl

/-- One binary allocation term in the derivative of a bilinear evaluation. -/
def q23BilinearAllocationTerm (B : E →L[𝕜] F →L[𝕜] G)
    (f : D → E) (g : D → F) (domain : Set D) {order : ℕ}
    (assignment : Fin order → Fin 2) (point : D)
    (directions : Fin order → D) : G :=
  B (iteratedFDerivWithin 𝕜 (assignmentFiber assignment 0).card f domain point
        (q23FiberTuple assignment 0 directions))
    (iteratedFDerivWithin 𝕜 (assignmentFiber assignment 1).card g domain point
      (q23FiberTuple assignment 1 directions))

/-- Sum over all choices of which factor receives each derivative direction. -/
def q23BilinearAllocationDerivative (B : E →L[𝕜] F →L[𝕜] G)
    (f : D → E) (g : D → F) (domain : Set D) (order : ℕ)
    (point : D) (directions : Fin order → D) : G :=
  ∑ assignment : Fin order → Fin 2,
    q23BilinearAllocationTerm B f g domain assignment point directions

theorem q23BilinearAllocationTerm_cons (B : E →L[𝕜] F →L[𝕜] G)
    (f : D → E) (g : D → F) (domain : Set D) {order : ℕ}
    (assignment : Fin order → Fin 2) (slot : Fin 2) (point : D)
    (directions : Fin (order + 1) → D) :
    q23BilinearAllocationTerm B f g domain (Fin.cons slot assignment) point directions =
      if slot = 0 then
        B (iteratedFDerivWithin 𝕜 ((assignmentFiber assignment 0).card + 1)
              f domain point
              (Fin.cons (directions 0) (q23FiberTuple assignment 0 (Fin.tail directions))))
          (iteratedFDerivWithin 𝕜 (assignmentFiber assignment 1).card
              g domain point (q23FiberTuple assignment 1 (Fin.tail directions)))
      else
        B (iteratedFDerivWithin 𝕜 (assignmentFiber assignment 0).card
              f domain point (q23FiberTuple assignment 0 (Fin.tail directions)))
          (iteratedFDerivWithin 𝕜 ((assignmentFiber assignment 1).card + 1)
              g domain point
              (Fin.cons (directions 0) (q23FiberTuple assignment 1 (Fin.tail directions)))) := by
  by_cases first : slot = 0
  · subst first
    rw [if_pos rfl]
    unfold q23BilinearAllocationTerm
    rw [q23FiberTuple_cons_self,
      q23FiberTuple_cons_of_ne assignment 0 1 (by decide),
      q23IteratedFDerivWithin_cast
        (card_assignmentFiber_cons_self assignment 0),
      q23IteratedFDerivWithin_cast
        (card_assignmentFiber_cons_of_ne assignment 0 1 (by decide))]
  · rw [if_neg first]
    have second : slot = 1 := Fin.eq_one_of_ne_zero slot first
    subst second
    unfold q23BilinearAllocationTerm
    rw [q23FiberTuple_cons_of_ne assignment 1 0 (by decide),
      q23FiberTuple_cons_self,
      q23IteratedFDerivWithin_cast
        (card_assignmentFiber_cons_of_ne assignment 1 0 (by decide)),
      q23IteratedFDerivWithin_cast
        (card_assignmentFiber_cons_self assignment 1)]

theorem q23_sum_assignments_cons {order : ℕ}
    (summand : (Fin (order + 1) → Fin 2) → G) :
    ∑ assignment : Fin (order + 1) → Fin 2, summand assignment =
      ∑ slot : Fin 2, ∑ tail : Fin order → Fin 2,
        summand (Fin.cons slot tail) := by
  calc
    _ = ∑ pair : Fin 2 × (Fin order → Fin 2),
        summand (Fin.cons pair.1 pair.2) :=
      ((Fin.consEquiv (fun _ : Fin (order + 1) => Fin 2)).sum_comp summand).symm
    _ = _ := Fintype.sum_prod_type _

/-- Exact independent-direction Leibniz formula on an open domain. -/
theorem iteratedFDerivWithin_bilinear_allocation_all_orders
    (B : E →L[𝕜] F →L[𝕜] G)
    (f : D → E) (g : D → F) (domain : Set D)
    (openDomain : IsOpen domain)
    (fSmooth : ContDiffOn 𝕜 ∞ f domain)
    (gSmooth : ContDiffOn 𝕜 ∞ g domain)
    (order : ℕ) (point : D) (inside : point ∈ domain)
    (directions : Fin order → D) :
    iteratedFDerivWithin 𝕜 order (fun x => B (f x) (g x)) domain point directions =
      q23BilinearAllocationDerivative B f g domain order point directions := by
  have unique : UniqueDiffOn 𝕜 domain := openDomain.uniqueDiffOn
  have productSmooth : ContDiffOn 𝕜 ∞ (fun x => B (f x) (g x)) domain :=
    B.isBoundedBilinearMap.contDiff.comp₂_contDiffOn fSmooth gSmooth
  induction order generalizing point with
  | zero =>
      unfold q23BilinearAllocationDerivative q23BilinearAllocationTerm
      rw [Fintype.sum_unique]
      change (B (f point)) (g point) =
        (B
          ((iteratedFDerivWithin 𝕜
              (assignmentFiber (default : Fin 0 → Fin 2) 0).card f domain point)
            (q23FiberTuple (default : Fin 0 → Fin 2) 0 directions)))
          ((iteratedFDerivWithin 𝕜
              (assignmentFiber (default : Fin 0 → Fin 2) 1).card g domain point)
            (q23FiberTuple (default : Fin 0 → Fin 2) 1 directions))
      have fiberCardZero (slot : Fin 2) :
          (assignmentFiber (default : Fin 0 → Fin 2) slot).card = 0 := by
        apply Finset.card_eq_zero.mpr
        exact Finset.eq_empty_of_forall_notMem (fun position _ => position.elim0)
      have fiberTupleZero (slot : Fin 2) :
          q23FiberTuple (default : Fin 0 → Fin 2) slot directions =
            (fun position : Fin 0 => position.elim0) ∘ Fin.cast (fiberCardZero slot) := by
        funext index
        exact (Fin.cast (fiberCardZero slot) index).elim0
      rw [fiberTupleZero 0,
        q23IteratedFDerivWithin_cast (fiberCardZero 0) f domain point,
        fiberTupleZero 1,
        q23IteratedFDerivWithin_cast (fiberCardZero 1) g domain point]
      simp only [iteratedFDerivWithin_zero_apply]
  | succ order inductionHypothesis =>
      let oldDirections : Fin order → D := Fin.tail directions
      let newDirection : D := directions 0
      have derivativeSmooth : DifferentiableWithinAt 𝕜
          (iteratedFDerivWithin 𝕜 order
            (fun x => B (f x) (g x)) domain) domain point :=
        (productSmooth.differentiableOn_iteratedFDerivWithin
          (by exact_mod_cast (WithTop.coe_lt_top order)) unique) point inside
      rw [iteratedFDerivWithin_succ_apply_left]
      rw [← fderivWithin_continuousMultilinear_apply_const_apply
        (unique point inside) derivativeSmooth oldDirections newDirection]
      have allocationEq : Set.EqOn
          (fun x => iteratedFDerivWithin 𝕜 order
            (fun y => B (f y) (g y)) domain x oldDirections)
          (fun x => q23BilinearAllocationDerivative B f g domain order x oldDirections)
          domain := by
        intro x hx
        exact inductionHypothesis x hx oldDirections
      rw [fderivWithin_congr allocationEq (allocationEq inside)]
      unfold q23BilinearAllocationDerivative
      have termDiff (assignment : Fin order → Fin 2) :
          DifferentiableWithinAt 𝕜
            (fun x => q23BilinearAllocationTerm B f g domain assignment x oldDirections)
            domain point := by
        have fDiff : DifferentiableWithinAt 𝕜
            (fun x => iteratedFDerivWithin 𝕜
              (assignmentFiber assignment 0).card f domain x
                (q23FiberTuple assignment 0 oldDirections)) domain point := by
          exact ((fSmooth.differentiableOn_iteratedFDerivWithin
            (by exact_mod_cast (WithTop.coe_lt_top (assignmentFiber assignment 0).card)) unique)
              point inside).continuousMultilinear_apply_const _
        have gDiff : DifferentiableWithinAt 𝕜
            (fun x => iteratedFDerivWithin 𝕜
              (assignmentFiber assignment 1).card g domain x
                (q23FiberTuple assignment 1 oldDirections)) domain point := by
          exact ((gSmooth.differentiableOn_iteratedFDerivWithin
            (by exact_mod_cast (WithTop.coe_lt_top (assignmentFiber assignment 1).card)) unique)
              point inside).continuousMultilinear_apply_const _
        unfold q23BilinearAllocationTerm
        exact (B.hasFDerivWithinAt_of_bilinear fDiff.hasFDerivWithinAt
          gDiff.hasFDerivWithinAt).differentiableWithinAt
      rw [fderivWithin_fun_sum (unique point inside) (fun assignment _ => termDiff assignment)]
      simp only [sum_apply]
      rw [q23_sum_assignments_cons, Fin.sum_univ_two, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro assignment _
      have fDiff : DifferentiableWithinAt 𝕜
          (fun x => iteratedFDerivWithin 𝕜
            (assignmentFiber assignment 0).card f domain x
              (q23FiberTuple assignment 0 oldDirections)) domain point := by
        exact ((fSmooth.differentiableOn_iteratedFDerivWithin
          (by exact_mod_cast (WithTop.coe_lt_top (assignmentFiber assignment 0).card)) unique)
            point inside).continuousMultilinear_apply_const _
      have gDiff : DifferentiableWithinAt 𝕜
          (fun x => iteratedFDerivWithin 𝕜
            (assignmentFiber assignment 1).card g domain x
              (q23FiberTuple assignment 1 oldDirections)) domain point := by
        exact ((gSmooth.differentiableOn_iteratedFDerivWithin
          (by exact_mod_cast (WithTop.coe_lt_top (assignmentFiber assignment 1).card)) unique)
            point inside).continuousMultilinear_apply_const _
      unfold q23BilinearAllocationTerm
      rw [B.fderivWithin_of_bilinear fDiff gDiff (unique point inside)]
      simp only [add_apply, ContinuousLinearMap.precompR_apply,
        ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply,
        ContinuousLinearMap.comp_apply]
      rw [fderivWithin_continuousMultilinear_apply_const_apply
        (unique point inside)
        ((gSmooth.differentiableOn_iteratedFDerivWithin
          (by exact_mod_cast (WithTop.coe_lt_top (assignmentFiber assignment 1).card)) unique)
            point inside) _ newDirection]
      rw [fderivWithin_continuousMultilinear_apply_const_apply
        (unique point inside)
        ((fSmooth.differentiableOn_iteratedFDerivWithin
          (by exact_mod_cast (WithTop.coe_lt_top (assignmentFiber assignment 0).card)) unique)
            point inside) _ newDirection]
      have gSucc :
          ((fderivWithin 𝕜
              (iteratedFDerivWithin 𝕜 (assignmentFiber assignment 1).card
                g domain) domain point) newDirection)
              (q23FiberTuple assignment 1 oldDirections) =
            iteratedFDerivWithin 𝕜 ((assignmentFiber assignment 1).card + 1)
              g domain point
              (Fin.cons newDirection (q23FiberTuple assignment 1 oldDirections)) := by
        rw [iteratedFDerivWithin_succ_apply_left]
        simp only [Fin.cons_zero, Fin.tail_cons]
      have fSucc :
          ((fderivWithin 𝕜
              (iteratedFDerivWithin 𝕜 (assignmentFiber assignment 0).card
                f domain) domain point) newDirection)
              (q23FiberTuple assignment 0 oldDirections) =
            iteratedFDerivWithin 𝕜 ((assignmentFiber assignment 0).card + 1)
              f domain point
              (Fin.cons newDirection (q23FiberTuple assignment 0 oldDirections)) := by
        rw [iteratedFDerivWithin_succ_apply_left]
        simp only [Fin.cons_zero, Fin.tail_cons]
      rw [gSucc, fSucc]
      change
        (B
            (iteratedFDerivWithin 𝕜 (assignmentFiber assignment 0).card f domain point
              (q23FiberTuple assignment 0 oldDirections)))
            (iteratedFDerivWithin 𝕜 ((assignmentFiber assignment 1).card + 1)
              g domain point
              (Fin.cons newDirection (q23FiberTuple assignment 1 oldDirections))) +
          (B
            (iteratedFDerivWithin 𝕜 ((assignmentFiber assignment 0).card + 1)
              f domain point
              (Fin.cons newDirection (q23FiberTuple assignment 0 oldDirections))))
            (iteratedFDerivWithin 𝕜 (assignmentFiber assignment 1).card g domain point
              (q23FiberTuple assignment 1 oldDirections)) =
        q23BilinearAllocationTerm B f g domain (Fin.cons 0 assignment) point directions +
          q23BilinearAllocationTerm B f g domain (Fin.cons 1 assignment) point directions
      rw [q23BilinearAllocationTerm_cons B f g domain assignment 0 point directions,
        q23BilinearAllocationTerm_cons B f g domain assignment 1 point directions]
      simp only [ite_true]
      rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]
      rw [add_comm]

/-- Global-derivative form at an interior point of the open domain. -/
theorem iteratedFDeriv_bilinear_allocation_all_orders
    (B : E →L[𝕜] F →L[𝕜] G)
    (f : D → E) (g : D → F) (domain : Set D)
    (openDomain : IsOpen domain)
    (fSmooth : ContDiffOn 𝕜 ∞ f domain)
    (gSmooth : ContDiffOn 𝕜 ∞ g domain)
    (order : ℕ) (point : D) (inside : point ∈ domain)
    (directions : Fin order → D) :
    iteratedFDeriv 𝕜 order (fun x => B (f x) (g x)) point directions =
      ∑ assignment : Fin order → Fin 2,
        B (iteratedFDeriv 𝕜 (assignmentFiber assignment 0).card f point
              (q23FiberTuple assignment 0 directions))
          (iteratedFDeriv 𝕜 (assignmentFiber assignment 1).card g point
            (q23FiberTuple assignment 1 directions)) := by
  rw [← iteratedFDerivWithin_of_isOpen order openDomain inside]
  rw [iteratedFDerivWithin_bilinear_allocation_all_orders B f g domain openDomain
    fSmooth gSmooth order point inside directions]
  unfold q23BilinearAllocationDerivative q23BilinearAllocationTerm
  apply Finset.sum_congr rfl
  intro assignment _
  rw [iteratedFDerivWithin_of_isOpen _ openDomain inside,
    iteratedFDerivWithin_of_isOpen _ openDomain inside]

end Bilinear

end Grad.NonlinearQuotientBounds
