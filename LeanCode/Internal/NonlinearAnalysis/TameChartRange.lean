import TameChartInterface

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct

/-! Conversions of the tower's range-list one-high forms into finite-tuple
form over `Fin order`, through the map and shift structure of `range`. -/

variable {parameters : PhaseParameters}

theorem lowIndexProd_map (directions : ℕ → TangentCoefficient parameters)
    (relabel : ℕ → ℕ) :
    ∀ indices : List ℕ, lowIndexProd directions (indices.map relabel) =
      lowIndexProd (directions ∘ relabel) indices := by
  intro indices
  induction indices with
  | nil =>
    rw [List.map_nil, lowIndexProd_nil, lowIndexProd_nil]
  | cons head tail inductive_step =>
    rw [List.map_cons, lowIndexProd_cons, lowIndexProd_cons, inductive_step]
    rfl

theorem oneHighIndex_map (grade : ℕ) (directions : ℕ → TangentCoefficient parameters)
    (relabel : ℕ → ℕ) :
    ∀ indices : List ℕ, oneHighIndex grade directions (indices.map relabel) =
      oneHighIndex grade (directions ∘ relabel) indices := by
  intro indices
  induction indices with
  | nil =>
    rw [List.map_nil, oneHighIndex_nil, oneHighIndex_nil]
  | cons head tail inductive_step =>
    rw [List.map_cons, oneHighIndex_cons, oneHighIndex_cons, inductive_step,
      ← lowIndexProd_map directions relabel tail]
    rfl

/-- The real-valued erase product through the `succAbove` embedding. -/
theorem real_prod_succAbove_eq_erase {order : ℕ} (index : Fin (order + 1))
    (values : Fin (order + 1) → ℝ) :
    ∏ position : Fin order, values (index.succAbove position) =
      ∏ other ∈ Finset.univ.erase index, values other := by
  rw [← Finset.compl_singleton, ← Fin.image_succAbove_univ index]
  rw [Finset.prod_image (fun _ _ _ _ equal => Fin.succAbove_right_injective equal)]

theorem lowIndexProd_range (directions : ℕ → TangentCoefficient parameters) :
    ∀ order : ℕ, lowIndexProd directions (List.range order) =
      ∏ index : Fin order, tangentPlanarEnvelope 0 (directions index.val) := by
  intro order
  induction order generalizing directions with
  | zero =>
    rw [List.range_zero, lowIndexProd_nil, Finset.univ_eq_empty, Finset.prod_empty]
  | succ smaller inductive_step =>
    rw [List.range_succ_eq_map, lowIndexProd_cons, lowIndexProd_map,
      inductive_step (directions ∘ (· + 1)), Fin.prod_univ_succ]
    simp only [Function.comp_apply, Fin.val_succ, Fin.val_zero]

/-- Splitting an erase product at the zeroth position. -/
theorem erase_succ_prod : ∀ {inner : ℕ} (index : Fin inner)
    (values : Fin (inner + 1) → ℝ),
    ∏ other ∈ Finset.univ.erase index.succ, values other =
      values 0 * ∏ other ∈ Finset.univ.erase index, values other.succ := by
  intro inner
  match inner with
  | 0 => exact fun index => index.elim0
  | inner + 1 =>
    intro index values
    rw [← real_prod_succAbove_eq_erase index.succ, Fin.prod_univ_succ,
      Fin.succ_succAbove_zero]
    congr 1
    rw [← real_prod_succAbove_eq_erase index]
    apply Finset.prod_congr rfl
    intro position _
    rw [Fin.succ_succAbove_succ]

/-- Splitting the erase product of the zero index. -/
theorem erase_zero_prod {inner : ℕ} (values : Fin (inner + 1) → ℝ) :
    ∏ other ∈ Finset.univ.erase (0 : Fin (inner + 1)), values other =
      ∏ position : Fin inner, values position.succ := by
  rw [← real_prod_succAbove_eq_erase (0 : Fin (inner + 1))]
  apply Finset.prod_congr rfl
  intro position _
  rw [Fin.zero_succAbove]

theorem oneHighIndex_range (grade : ℕ) (directions : ℕ → TangentCoefficient parameters) :
    ∀ order : ℕ, oneHighIndex grade directions (List.range order) =
      ∑ index : Fin order, tangentPlanarEnvelope grade (directions index.val) *
        ∏ other ∈ Finset.univ.erase index,
          tangentPlanarEnvelope 0 (directions other.val) := by
  intro order
  induction order generalizing directions with
  | zero =>
    rw [List.range_zero, oneHighIndex_nil, Finset.univ_eq_empty, Finset.sum_empty]
  | succ smaller inductive_step =>
    rw [List.range_succ_eq_map, oneHighIndex_cons, lowIndexProd_map,
      lowIndexProd_range (directions ∘ (· + 1)) smaller,
      oneHighIndex_map, inductive_step (directions ∘ (· + 1)), Fin.sum_univ_succ]
    congr 1
    · -- The zero term: its erase product runs over the successors.
      congr 1
      rw [erase_zero_prod]
      simp only [Function.comp_apply, Fin.val_succ]
    · -- The successor terms: shift each erase product back by one.
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _
      rw [erase_succ_prod index
        (fun other => tangentPlanarEnvelope 0 (directions other.val))]
      simp only [Function.comp_apply, Fin.val_succ, Fin.val_zero]
      ring

end Grad.NonlinearQuotientBounds
