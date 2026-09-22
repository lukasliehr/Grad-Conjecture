import ArrayPullback
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.KernelArrays

namespace Grad.TensorLpExchange

abbrev OrderedCellValues (rank : ℕ) :=
  PiLp 2 (fun _ : Fin rank → Fin 2 => CellValues)

abbrev OrderedValueField (rank : ℕ) :=
  Lp (OrderedCellValues rank) 2 (volume : Measure Spatial)

def ExchangeGoal : Prop :=
  ∀ rank : ℕ, ∃ exchange : OrderedFields rank ≃ₗᵢ[ℂ] OrderedValueField rank,
    (∀ field : OrderedFields rank,
      (exchange field : Spatial → OrderedCellValues rank) =ᵐ[volume]
        fun point => WithLp.toLp 2 (fun word => (field word : Spatial → CellValues) point)) ∧
    (∀ field : OrderedValueField rank, ∀ᵐ point ∂(volume : Measure Spatial),
      ∀ word : Fin rank → Fin 2,
        (exchange.symm field word : Spatial → CellValues) point = field point word)

end Grad.TensorLpExchange
