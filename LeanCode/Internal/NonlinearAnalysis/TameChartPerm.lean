import TameChartTowerDeriv

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! The exact-once direction accounting of the tower terms: the index list
of every level-`j` term is a permutation of `range j`, so each direction is
consumed by exactly one factor. -/

variable {parameters : PhaseParameters}

/-- All direction indices of a term, singles first. -/
def termIndexList (term : ChartTermData) : List ℕ :=
  term.singles ++ term.pairs.flatMap (fun pair => [pair.1, pair.2])

theorem termIndexList_g_child (newIndex : ℕ) (term : ChartTermData) :
    termIndexList ⟨term.gOrder + 1, term.pairs, newIndex :: term.singles⟩ =
      newIndex :: termIndexList term := by
  rw [termIndexList, termIndexList]
  rfl

/-- The single-replacement children permute one single into a pair. -/
theorem singlesChildren_perm (newIndex gOrder : ℕ) (pairs : List (ℕ × ℕ)) :
    ∀ singles : List ℕ, ∀ child ∈ singlesChildren newIndex gOrder pairs singles,
    (termIndexList child).Perm
      (newIndex :: (singles ++ pairs.flatMap (fun pair => [pair.1, pair.2]))) := by
  intro singles
  induction singles with
  | nil =>
    intro child membership
    exact absurd membership (List.not_mem_nil)
  | cons head tail inductive_step =>
    intro child membership
    rw [singlesChildren] at membership
    rcases List.mem_cons.mp membership with head_case | tail_case
    · subst head_case
      show (tail ++ (newIndex :: head :: pairs.flatMap (fun pair => [pair.1, pair.2]))).Perm
        (newIndex :: ((head :: tail) ++ pairs.flatMap (fun pair => [pair.1, pair.2])))
      have front := List.perm_append_comm
        (l₁ := tail)
        (l₂ := newIndex :: head :: pairs.flatMap (fun pair => [pair.1, pair.2]))
      have inner := List.perm_append_comm
        (l₁ := pairs.flatMap (fun pair => [pair.1, pair.2])) (l₂ := tail)
      exact front.trans ((inner.cons head).cons newIndex)
    · obtain ⟨inner, inner_mem, inner_eq⟩ := List.mem_map.mp tail_case
      have inner_perm := inductive_step inner inner_mem
      subst inner_eq
      have consed : termIndexList ⟨inner.gOrder, inner.pairs, head :: inner.singles⟩ =
          head :: termIndexList inner := by
        rw [termIndexList, termIndexList]
        rfl
      rw [consed]
      have lifted := inner_perm.cons head
      have swapped := List.Perm.swap newIndex head
        (tail ++ pairs.flatMap (fun pair => [pair.1, pair.2]))
      exact lifted.trans swapped

theorem chartTermChildren_perm (newIndex : ℕ) (term : ChartTermData) :
    ∀ child ∈ chartTermChildren newIndex term,
    (termIndexList child).Perm (newIndex :: termIndexList term) := by
  intro child membership
  rw [chartTermChildren] at membership
  rcases List.mem_cons.mp membership with g_case | singles_case
  · subst g_case
    rw [termIndexList_g_child]
  · exact singlesChildren_perm newIndex term.gOrder term.pairs term.singles child singles_case

/-- Exact-once accounting: the index list of every level-`j` term is a
permutation of `range j`. -/
theorem chartTerms_perm : ∀ level : ℕ, ∀ term ∈ chartTerms level,
    (termIndexList term).Perm (List.range level) := by
  intro level
  induction level with
  | zero =>
    intro term membership
    rw [chartTerms] at membership
    rcases List.mem_cons.mp membership with base_case | absurd_case
    · subst base_case
      rw [termIndexList]
      rfl
    · exact absurd absurd_case (List.not_mem_nil)
  | succ smaller inductive_step =>
    intro term membership
    rw [chartTerms] at membership
    obtain ⟨parent, parent_mem, child_mem⟩ := List.mem_flatMap.mp membership
    have parent_perm := inductive_step parent parent_mem
    have child_perm := chartTermChildren_perm smaller parent term child_mem
    have lifted := parent_perm.cons smaller
    have range_step : (smaller :: List.range smaller).Perm (List.range (smaller + 1)) := by
      rw [List.range_succ]
      exact List.perm_append_comm (l₁ := [smaller]) (l₂ := List.range smaller)
    exact (child_perm.trans lifted).trans range_step

end Grad.NonlinearQuotientBounds
