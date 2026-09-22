import AKCC6FixedPositiveAllocationVanishes

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000

open MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.RepresentedKernel Grad.RepresentedKernel.SpatialProduct Grad.RepresentedKernel.WeakDerivatives

theorem startupEmpty_complement_card (rank : ℕ) : ((∅ : Finset (Fin rank))ᶜ).card = rank := by simp

theorem startupFull_orderEmbedding (rank : ℕ)
    (position : Fin ((∅ : Finset (Fin rank))ᶜ).card) :
    ((∅ : Finset (Fin rank))ᶜ).orderEmbOfFin rfl position =
      Fin.cast (startupEmpty_complement_card rank) position := by
  let embedding : Fin rank ↪o Fin rank :=
    (Fin.castOrderIso (startupEmpty_complement_card rank).symm).toOrderEmbedding.trans
      (((∅ : Finset (Fin rank))ᶜ).orderEmbOfFin rfl)
  have identity (index : Fin rank) : embedding index = index :=
    le_antisymm (embedding.strictMono.le_id index) (embedding.strictMono.id_le index)
  have same := identity (Fin.cast (startupEmpty_complement_card rank) position)
  change (((∅ : Finset (Fin rank))ᶜ).orderEmbOfFin rfl)
    (Fin.cast (startupEmpty_complement_card rank).symm (Fin.cast (startupEmpty_complement_card rank) position)) = _ at same
  have cancel : Fin.cast (startupEmpty_complement_card rank).symm
      (Fin.cast (startupEmpty_complement_card rank) position) = position := by
    apply Fin.ext
    rfl
  rw [cancel] at same
  exact same

theorem startupFull_subword (rank : ℕ) (word : DerivativeIndex rank) :
    subword word (∅ : Finset (Fin rank))ᶜ =
      (fun position => word (Fin.cast (startupEmpty_complement_card rank) position)) := by
  funext position
  exact congrArg word (startupFull_orderEmbedding rank position)

theorem startupEmpty_selectedIndex (rank : ℕ) (word : DerivativeIndex rank) :
    selectedIndex word (∅ : Finset (Fin rank)) = (0, 0) := by
  have total := allocationIndices rank word ∅
  simp only [Finset.card_empty] at total
  exact Prod.ext (by omega) (by omega)

end Grad.CartesianStartup
