import SP1Interface
import Mathlib.Order.Fin.Tuple

noncomputable section

open Grad.PDEBootstrap
open scoped BigOperators ContDiff

namespace Grad.RepresentedKernel.SpatialProduct

def liftSelected {rank : ℕ} (selected : Finset (Fin rank)) : Finset (Fin (rank + 1)) :=
  selected.map (Fin.succEmb rank)

def headSelected {rank : ℕ} (selected : Finset (Fin rank)) : Finset (Fin (rank + 1)) :=
  insert 0 (liftSelected selected)

def dropSelected {rank : ℕ} (selected : Finset (Fin (rank + 1))) : Finset (Fin rank) :=
  Finset.univ.filter (fun position => position.succ ∈ selected)

@[simp] theorem zero_not_mem_lift {rank : ℕ} (selected : Finset (Fin rank)) :
    (0 : Fin (rank + 1)) ∉ liftSelected selected := by
  simp [liftSelected]

@[simp] theorem succ_mem_lift {rank : ℕ} (selected : Finset (Fin rank)) (position : Fin rank) :
    position.succ ∈ liftSelected selected ↔ position ∈ selected := by
  simp [liftSelected]

@[simp] theorem zero_mem_head {rank : ℕ} (selected : Finset (Fin rank)) :
    (0 : Fin (rank + 1)) ∈ headSelected selected := by
  simp [headSelected]

@[simp] theorem succ_mem_head {rank : ℕ} (selected : Finset (Fin rank)) (position : Fin rank) :
    position.succ ∈ headSelected selected ↔ position ∈ selected := by
  simp [headSelected]

@[simp] theorem mem_drop {rank : ℕ} (selected : Finset (Fin (rank + 1))) (position : Fin rank) :
    position ∈ dropSelected selected ↔ position.succ ∈ selected := by
  simp [dropSelected]

@[simp] theorem drop_lift {rank : ℕ} (selected : Finset (Fin rank)) :
    dropSelected (liftSelected selected) = selected := by
  ext position
  simp

@[simp] theorem drop_head {rank : ℕ} (selected : Finset (Fin rank)) :
    dropSelected (headSelected selected) = selected := by
  ext position
  simp

@[simp] theorem lift_compl {rank : ℕ} (selected : Finset (Fin rank)) :
    (liftSelected selected)ᶜ = headSelected selectedᶜ := by
  ext position
  refine Fin.cases ?_ (fun previous => ?_) position <;> simp

@[simp] theorem head_compl {rank : ℕ} (selected : Finset (Fin rank)) :
    (headSelected selected)ᶜ = liftSelected selectedᶜ := by
  ext position
  refine Fin.cases ?_ (fun previous => ?_) position <;> simp

def allocationEquiv (rank : ℕ) :
    Finset (Fin rank) ⊕ Finset (Fin rank) ≃ Finset (Fin (rank + 1)) where
  toFun := Sum.elim liftSelected headSelected
  invFun selected := if 0 ∈ selected then Sum.inr (dropSelected selected)
    else Sum.inl (dropSelected selected)
  left_inv selected := by
    cases selected <;> simp
  right_inv selected := by
    dsimp only
    split_ifs with contains
    · ext position
      refine Fin.cases ?_ (fun previous => ?_) position <;> simp [contains]
    · ext position
      refine Fin.cases ?_ (fun previous => ?_) position <;> simp [contains]

theorem sum_allocations {Result : Type*} [AddCommMonoid Result] (rank : ℕ)
    (function : Finset (Fin (rank + 1)) → Result) :
    ∑ selected, function selected =
      (∑ selected : Finset (Fin rank), function (liftSelected selected)) +
      ∑ selected : Finset (Fin rank), function (headSelected selected) := by
  rw [← (allocationEquiv rank).sum_comp function, Fintype.sum_sum_type]
  rfl

theorem positions : PositionGoal := by
  intro rank selected
  refine ⟨?_, (selected.orderEmbOfFin rfl).strictMono, selected.orderEmbOfFin_mem rfl⟩
  simp [Finset.card_add_card_compl]

theorem selectedDerivative_eq {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {rank count : ℕ} (directions : Fin rank → Spatial) (selected : Finset (Fin rank))
    (cardinality : selected.card = count) (enumeration : Fin count → Fin rank)
    (membership : ∀ position, enumeration position ∈ selected) (increasing : StrictMono enumeration)
    (function : Spatial → Value) (point : Spatial) :
    selectedDerivative directions selected function point =
      iteratedFDeriv ℝ count function point (fun position => directions (enumeration position)) := by
  subst count
  rw [Finset.orderEmbOfFin_unique rfl membership increasing]
  rfl

theorem selectedDerivative_lift {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {rank : ℕ} (directions : Fin (rank + 1) → Spatial) (selected : Finset (Fin rank))
    (function : Spatial → Value) (point : Spatial) :
    selectedDerivative directions (liftSelected selected) function point =
      selectedDerivative (Fin.tail directions) selected function point := by
  apply selectedDerivative_eq directions (liftSelected selected) (by simp [liftSelected])
    (fun position => (selected.orderEmbOfFin rfl position).succ)
  · intro position
    simp
  · exact Fin.strictMono_succ.comp (selected.orderEmbOfFin rfl).strictMono

theorem selectedDerivative_head {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {rank : ℕ} (directions : Fin (rank + 1) → Spatial) (selected : Finset (Fin rank))
    (function : Spatial → Value) (point : Spatial) :
    selectedDerivative directions (headSelected selected) function point =
      iteratedFDeriv ℝ (selected.card + 1) function point
        (Fin.cons (directions 0)
          (fun position => directions (selected.orderEmbOfFin rfl position).succ)) := by
  have enumeration := selectedDerivative_eq directions (headSelected selected)
    (show (headSelected selected).card = selected.card + 1 by simp [headSelected, liftSelected])
    (Fin.cons 0 (fun position => (selected.orderEmbOfFin rfl position).succ))
    (by intro position; refine Fin.cases ?_ (fun previous => ?_) position <;> simp)
    (Fin.strictMono_cons.mpr ⟨fun _ => Fin.succ_pos _,
      Fin.strictMono_succ.comp (selected.orderEmbOfFin rfl).strictMono⟩) function point
  convert enumeration using 1
  congr 1
  funext position
  refine Fin.cases ?_ (fun previous => ?_) position <;> simp

end Grad.RepresentedKernel.SpatialProduct
