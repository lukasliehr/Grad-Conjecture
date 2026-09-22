import ANG15FirstAngularEstimate
import Mathlib.Analysis.InnerProductSpace.Subspace

noncomputable section
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 100000
open scoped BigOperators
namespace Grad.CircularHighWeak

section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

private def projectionSpace (projections : ℤ → E →L[ℂ] E) (mode : ℤ) : Submodule ℂ E :=
  (projections mode).toLinearMap.range

private theorem projectionSpaces_orthogonal (projections : ℤ → E →L[ℂ] E)
    (symmetric : ∀ mode first second, inner ℂ (projections mode first) second = inner ℂ first (projections mode second))
    (disjoint : ∀ first second, first ≠ second → ∀ field, projections first (projections second field) = 0) :
    OrthogonalFamily ℂ (fun mode : ℤ => projectionSpace projections mode)
      (fun mode => (projectionSpace projections mode).subtypeₗᵢ) := by
  intro first second different value test
  rcases value.property with ⟨field, equalField⟩
  rcases test.property with ⟨probe, equalProbe⟩
  change inner ℂ value.val test.val = 0
  exact ((congrArg₂ (fun first second : E => inner ℂ first second) equalField.symm equalProbe.symm).trans
    ((symmetric first field (projections second probe)).trans
      (congrArg (fun value : E => inner ℂ field value) (disjoint first second different probe)))).trans (inner_zero_right _)

private def weightedProjection (projections : ℤ → E →L[ℂ] E) (coefficient : ℤ → ℂ) (field : E) (mode : ℤ) :
    projectionSpace projections mode :=
  ⟨coefficient mode • projections mode field,
    ⟨coefficient mode • field, (projections mode).map_smul (coefficient mode) field⟩⟩

private theorem projectionSeries_summable [CompleteSpace E] (projections : ℤ → E →L[ℂ] E)
    (symmetric : ∀ mode first second, inner ℂ (projections mode first) second = inner ℂ first (projections mode second))
    (disjoint : ∀ first second, first ≠ second → ∀ field, projections first (projections second field) = 0)
    (coefficient : ℤ → ℂ) (field : E) (bound : ℝ)
    (bounded : ∀ modes : Finset ℤ, ‖∑ mode ∈ modes, coefficient mode • projections mode field‖ ≤ bound) :
    Summable (fun mode => coefficient mode • projections mode field) := by
  have orthogonal := projectionSpaces_orthogonal projections symmetric disjoint
  have squares : Summable (fun mode => ‖weightedProjection projections coefficient field mode‖ ^ 2) := by
    apply summable_of_sum_le (fun _ => sq_nonneg _) (c := bound ^ 2)
    intro modes
    have norm := orthogonal.norm_sum (weightedProjection projections coefficient field) modes
    have estimate := pow_le_pow_left₀ (norm_nonneg _) (bounded modes) 2
    exact norm.symm.le.trans estimate
  exact (orthogonal.summable_iff_norm_sq_summable (weightedProjection projections coefficient field)).mpr squares
end Generic

/-- A bounded family of finite orthogonal H1 sums converges in actual H1. -/
theorem highModeSeries_summable (coefficient : ℤ → ℂ) (field : highDiskGrade) (bound : ℝ)
    (_positive : 0 ≤ bound)
    (bounded : ∀ modes : Finset ℤ, ‖∑ mode ∈ modes, coefficient mode • highDiskMode mode field‖ ≤ bound) :
    Summable (fun mode => coefficient mode • highDiskMode mode field) :=
  projectionSeries_summable highDiskMode highDiskMode_symmetric
    (fun first second different field => (highDiskMode_projection first second field).trans (if_neg different))
    coefficient field bound bounded

theorem highModeSeries_bound (coefficient : ℤ → ℂ) (field : highDiskGrade) (bound : ℝ)
    (positive : 0 ≤ bound)
    (bounded : ∀ modes : Finset ℤ, ‖∑ mode ∈ modes, coefficient mode • highDiskMode mode field‖ ≤ bound) :
    ‖∑' mode, coefficient mode • highDiskMode mode field‖ ≤ bound := by
  have summable := highModeSeries_summable coefficient field bound positive bounded
  exact le_of_tendsto (continuous_norm.tendsto _ |>.comp summable.hasSum) (Filter.Eventually.of_forall bounded)

end Grad.CircularHighWeak
