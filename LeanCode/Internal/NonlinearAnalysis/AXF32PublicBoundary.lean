import AXF31CompletedFiniteDensity

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.CartesianState Grad.QuotientProjection Grad.RealFixedRanges Grad.ChartAxisProjections
open Grad.CompletedReality

/-- Full original Cartesian same-grade flat-source projection and actual
completed finite-cell density. The norm is BS3, not a substitute norm. -/
def OriginalCartesianFlatBoundaryGoal : Prop :=
  ∀ parameters : PhaseParameters,
    (∀ grade : ℕ, ∀ source : SmoothQuotient parameters,
      cartesianSourceNorm grade (spinCartesianEquiv source) = quotientNorm parameters grade source) ∧
    (∀ source : CartesianSourceCore parameters,
      source ∈ LinearMap.range (cartesianFlatProjection (parameters := parameters)) ↔
        CartesianCoreIsFlat source) ∧
    (∀ source : CartesianSourceCore parameters,
      cartesianFlatProjection (cartesianFlatProjection source) = cartesianFlatProjection source) ∧
    (∀ grade : ℕ, 3 ≤ grade → ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ source : CartesianSourceCore parameters,
        cartesianSourceNorm grade (cartesianFlatProjection source) ≤ constant * cartesianSourceNorm grade source) ∧
    (∀ source : SmoothQuotient parameters,
      zCoreConjugation parameters source = source ↔
        cartesianSourceConjugation (spinCartesianEquiv source) = spinCartesianEquiv source) ∧
    (∀ (cellLength : ℝ) (positive : 0 < cellLength) (grade : ℕ) (large : 3 ≤ grade),
      DenseRange (flatSmoothEmbedding parameters cellLength positive grade large) ∧
      Function.Injective (flatSmoothEmbedding parameters cellLength positive grade large) ∧
      (∀ source : LinearMap.ker (realExtraction parameters cellLength),
        ‖flatSmoothEmbedding parameters cellLength positive grade large source‖ =
          cartesianSourceNorm grade (spinCartesianEquiv source.val.val)) ∧
      (∀ (source : flatSourceRange parameters grade large) (epsilon : ℝ), 0 < epsilon →
        ∃ (core : LinearMap.ker (realExtraction parameters cellLength)) (cutoff : ℕ),
          (∀ cell : ℤ, cell ∉ centeredCellBox cutoff → ∀ row : Fin 4,
            ((core.val.val row).val cell) = 0) ∧
          dist (flatSmoothEmbedding parameters cellLength positive grade large core) source < epsilon)) ∧
    (∀ (lower upper : ℕ) (large : 3 ≤ lower) (ordered : lower ≤ upper),
      Function.Injective (flatSourceLowering parameters large ordered) ∧
        ∀ source : flatSourceRange parameters upper (large.trans ordered),
          ‖flatSourceLowering parameters large ordered source‖ ≤ ‖source‖)

theorem actualOriginalCartesianFlatBoundary : OriginalCartesianFlatBoundaryGoal := by
  intro parameters
  refine ⟨spinCartesianEquiv_norm, cartesianFlatProjection_range,
    cartesianFlatProjection_idempotent, cartesianFlatProjection_bound parameters,
    spinCartesianEquiv_real_iff, ?_, ?_⟩
  · intro cellLength positive grade large
    exact ⟨flatSmoothEmbedding_denseRange parameters cellLength positive grade large,
      flatSmoothEmbedding_injective parameters cellLength positive grade large,
      flatSmoothEmbedding_cartesian_norm parameters cellLength positive grade large,
      completedFlatSource_finiteApproximation parameters cellLength positive grade large⟩
  · intro lower upper large ordered
    exact ⟨flatSourceLowering_injective parameters large ordered,
      flatSourceLowering_norm_le parameters large ordered⟩

end Grad.FlatSourceProjection
