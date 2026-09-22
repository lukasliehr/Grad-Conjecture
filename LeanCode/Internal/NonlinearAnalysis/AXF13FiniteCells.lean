import AXF12CellLocality
import FC7Truncation

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.NonlinearQuotientBounds Grad.QuotientProjection Grad.AxisCore

variable {parameters : PhaseParameters}

theorem flatSourceProjection_congr_cell (first second : SmoothQuotient parameters)
    (cell : ℤ) (same : ∀ row, (first row).val cell = (second row).val cell) (row : Fin 4) :
    ((flatSourceProjection first) row).val cell = ((flatSourceProjection second) row).val cell := by
  have zero : ∀ row, ((first - second) row).val cell = 0 := by
    intro row
    change (first row).val cell - (second row).val cell = 0
    exact sub_eq_zero.mpr (same row)
  have law := flatSourceProjection_zero_cell (first - second) cell zero row
  rw [map_sub] at law
  exact sub_eq_zero.mp law

def sourceCellTruncation (parameters : PhaseParameters) (cutoff : ℕ) :
    SmoothQuotient parameters →ₗ[ℂ] SmoothQuotient parameters :=
  LinearMap.pi (fun row => (cartesianCoreTruncation parameters cutoff).comp (LinearMap.proj row))

theorem sourceCellTruncation_apply (cutoff : ℕ) (source : SmoothQuotient parameters)
    (row : Fin 4) (cell : ℤ) :
    ((sourceCellTruncation parameters cutoff source) row).val cell =
      if cell ∈ centeredCellBox cutoff then (source row).val cell else 0 := rfl

/-- The actual fixed flattening commutes with the accepted centered cell truncation. -/
theorem flatSourceProjection_truncation (cutoff : ℕ) (source : SmoothQuotient parameters) :
    flatSourceProjection (sourceCellTruncation parameters cutoff source) =
      sourceCellTruncation parameters cutoff (flatSourceProjection source) := by
  funext row
  apply Subtype.ext
  funext cell
  rw [sourceCellTruncation_apply]
  by_cases inside : cell ∈ centeredCellBox cutoff
  · rw [if_pos inside]
    apply flatSourceProjection_congr_cell
    intro index
    rw [sourceCellTruncation_apply, if_pos inside]
  · rw [if_neg inside]
    apply flatSourceProjection_zero_cell
    intro index
    rw [sourceCellTruncation_apply, if_neg inside]

theorem sourceCellTruncation_flat (cutoff : ℕ) (source : SmoothQuotient parameters)
    (flat : IsFlat source) : IsFlat (sourceCellTruncation parameters cutoff source) := by
  have fixed : flatSourceProjection (sourceCellTruncation parameters cutoff source) =
      sourceCellTruncation parameters cutoff source := by
    rw [flatSourceProjection_truncation, flatSourceProjection_fixes source flat]
  rw [← fixed]
  exact flatSourceProjection_flat _

theorem flatSourceProjection_finite_cells (source : SmoothQuotient parameters)
    (cells : Finset ℤ) (supported : ∀ cell, cell ∉ cells → ∀ row, (source row).val cell = 0) :
    ∀ cell, cell ∉ cells → ∀ row, ((flatSourceProjection source) row).val cell = 0 := by
  intro cell outside row
  exact flatSourceProjection_zero_cell source cell (supported cell outside) row

end Grad.FlatSourceProjection
