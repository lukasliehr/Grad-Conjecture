import AXF10RealConsumer

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.CartesianState Grad.QuotientProjection Grad.RealFixedRanges Grad.ChartAxisProjections

/-- Shared original-spin interface for the flat-source completion. This does
not package the still separate BS2 Cartesian-vector isometry/formula review. -/
def OriginalSpinFlatProjectorGoal : Prop :=
  ∀ parameters : PhaseParameters,
    (∀ source : SmoothQuotient parameters,
      source ∈ LinearMap.range (flatSourceProjection (parameters := parameters)) ↔ IsFlat source) ∧
    (∀ source : SmoothQuotient parameters,
      flatSourceProjection (flatSourceProjection source) = flatSourceProjection source) ∧
    (∀ grade : ℕ, 3 ≤ grade → ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ source : SmoothQuotient parameters, quotientNorm parameters grade (flatSourceProjection source) ≤
        constant * quotientNorm parameters grade source) ∧
    (∀ cellLength : ℝ, 0 < cellLength →
      LinearMap.range (realFlatSourceProjection (parameters := parameters)) =
        LinearMap.ker (realExtraction parameters cellLength)) ∧
    (∀ grade : ℕ, ∀ large : 3 ≤ grade, ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ source : sourceSmoothRange parameters,
        ‖sourceSmoothEmbedding parameters grade large (realFlatSourceProjection source)‖ ≤
          constant * ‖sourceSmoothEmbedding parameters grade large source‖)

theorem actualOriginalSpinFlatProjector : OriginalSpinFlatProjectorGoal := by
  intro parameters
  exact ⟨flatSourceProjection_range, flatSourceProjection_idempotent,
    flatSourceProjection_bound parameters, realFlatSourceProjection_range,
    realFlatSourceProjection_bound parameters⟩

end Grad.FlatSourceProjection
