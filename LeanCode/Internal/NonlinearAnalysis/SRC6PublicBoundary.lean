import SRC5BulkNorm

noncomputable section

namespace Grad.SourceCollarBulk

open Grad.CartesianState Grad.AxisCore Grad.QuotientProjection
open Grad.SourceCollarDivision

/-- Exact completed BS36 consumer.  The constant is uniform in the collar
radius `lower`; `F0`, `RF0`, and the retained strong `F1` all carry both
weak radial rows at angular power `t+1`, while `F2=h/L` carries both rows at
power `t`.  The right side is the unchanged original fourfold Hilbert source
norm. -/
theorem actualCompletedSourceBulkConversion
    (parameters : PhaseParameters) (L : ℝ) (LPositive : 0 < L)
    (tangential : ℕ) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
        (source : ZAmbient parameters (tangential + 2)),
        ‖completedForceTangential lower positive bounded parameters tangential source‖ ≤
            constant * ‖source‖ ∧
          ‖completedForceAngular lower positive bounded parameters tangential source‖ ≤
            constant * ‖source‖ ∧
          ‖completedForceRadial lower positive bounded parameters tangential source‖ ≤
            constant * ‖source‖ ∧
          ‖completedFourthSource lower positive bounded parameters L tangential source‖ ≤
            constant * ‖source‖ := by
  refine ⟨sourceBulkConstant L tangential,
    sourceBulkConstant_positive L LPositive tangential, ?_⟩
  intro lower positive bounded source
  have total := completedSourceBulk_bound lower positive bounded parameters L LPositive tangential source
  have forceNonnegative := norm_nonneg
    (completedForceTangential lower positive bounded parameters tangential source)
  have angularNonnegative := norm_nonneg
    (completedForceAngular lower positive bounded parameters tangential source)
  have radialNonnegative := norm_nonneg
    (completedForceRadial lower positive bounded parameters tangential source)
  have fourthNonnegative := norm_nonneg
    (completedFourthSource lower positive bounded parameters L tangential source)
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Dense-core consumer tying the literal all-row graph formula and genuine
angular derivative to the exact original source norm.  This is the interface
used by the independent endpoint trace construction. -/
theorem actualSmoothSourceBulkCoreConsumer
    (parameters : PhaseParameters) (L : ℝ) (LPositive : 0 < L)
    (tangential : ℕ) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
        (source : SmoothQuotient parameters) (index : Fin 2) (mode : ℤ × ℤ),
        (completedForceAngular lower positive bounded parameters tangential
            (quotientEta parameters (tangential + 2) source)).val index mode =
          annularAngularRatio mode •
            (completedForceTangential lower positive bounded parameters tangential
              (quotientEta parameters (tangential + 2) source)).val index mode ∧
        ‖completedForceTangential lower positive bounded parameters tangential
              (quotientEta parameters (tangential + 2) source)‖ +
            ‖completedForceAngular lower positive bounded parameters tangential
              (quotientEta parameters (tangential + 2) source)‖ +
            ‖completedForceRadial lower positive bounded parameters tangential
              (quotientEta parameters (tangential + 2) source)‖ +
            ‖completedFourthSource lower positive bounded parameters L tangential
              (quotientEta parameters (tangential + 2) source)‖ ≤
          constant * ‖quotientEta parameters (tangential + 2) source‖ := by
  refine ⟨sourceBulkConstant L tangential,
    sourceBulkConstant_positive L LPositive tangential, ?_⟩
  intro lower positive bounded source index mode
  exact ⟨completedForceAngular_core_row lower positive bounded parameters tangential
      source index mode,
    completedSourceBulk_bound lower positive bounded parameters L LPositive tangential
      (quotientEta parameters (tangential + 2) source)⟩

end Grad.SourceCollarBulk
