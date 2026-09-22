import AXF30CartesianReality

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

open Filter
open scoped Topology

namespace Grad.FlatSourceProjection

open Grad.CartesianState Grad.RealFixedRanges Grad.ChartAxisProjections Grad.QuotientProjection

/-- Arbitrary completed original flat sources admit actual real, smooth,
finite-cell flat approximants in the unchanged norm. -/
theorem completedFlatSource_finiteApproximation (parameters : PhaseParameters)
    (cellLength : ℝ) (positive : 0 < cellLength) (grade : ℕ) (large : 3 ≤ grade)
    (source : flatSourceRange parameters grade large) (epsilon : ℝ) (epsilonPositive : 0 < epsilon) :
    ∃ (core : LinearMap.ker (realExtraction parameters cellLength)) (cutoff : ℕ),
      (∀ cell : ℤ, cell ∉ centeredCellBox cutoff → ∀ row : Fin 4,
        ((core.val.val row).val cell) = 0) ∧
      dist (flatSmoothEmbedding parameters cellLength positive grade large core) source < epsilon := by
  have halfPositive : 0 < epsilon / 2 := half_pos epsilonPositive
  obtain ⟨core, close⟩ := Metric.denseRange_iff.mp
    (flatSmoothEmbedding_denseRange parameters cellLength positive grade large)
    source (epsilon / 2) halfPositive
  have approximation := Metric.tendsto_nhds.mp
    (realFlatCellTruncation_tendsto parameters cellLength positive grade large core)
    (epsilon / 2) halfPositive
  obtain ⟨cutoff, cutoffClose⟩ := approximation.exists
  refine ⟨realFlatCellTruncation parameters cellLength positive cutoff core, cutoff, ?_, ?_⟩
  · exact fun cell outside row =>
      realFlatCellTruncation_outside parameters cellLength positive cutoff core cell outside row
  · calc
      _ ≤ dist (flatSmoothEmbedding parameters cellLength positive grade large
          (realFlatCellTruncation parameters cellLength positive cutoff core))
            (flatSmoothEmbedding parameters cellLength positive grade large core) +
        dist (flatSmoothEmbedding parameters cellLength positive grade large core) source :=
        dist_triangle _ _ _
      _ < epsilon / 2 + epsilon / 2 := add_lt_add cutoffClose (by simpa only [dist_comm] using close)
      _ = epsilon := add_halves epsilon

end Grad.FlatSourceProjection
