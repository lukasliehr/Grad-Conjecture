import AIS3OriginalHighDataCarrier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators

namespace Grad.AnnularCurrentSource

open Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularCurrentEnergy
open Grad.ActualBoundaryPrimitives

/-- The balanced packaging is exactly the Hilbert sum of BF2's eleven
independently normed coordinates. -/
theorem actualHighKnownAmbient_norm_sq (parameters : PhaseParameters) (lower : ℝ)
    (angular cell : ℕ) (data : ActualHighKnownAmbient parameters lower angular cell) :
    ‖data‖ ^ 2 =
      ‖highKnownWeightedProjection parameters lower angular cell data‖ ^ 2 +
      ‖highKnownAuxiliaryProjection parameters lower angular cell data‖ ^ 2 +
      ‖highKnownF0GraphProjection parameters lower angular cell data‖ ^ 2 +
      ‖highKnownF2GraphProjection parameters lower angular cell data‖ ^ 2 +
      ‖highKnownDatumProjection parameters lower angular cell data‖ ^ 2 +
      ‖highKnownIncomingProjection parameters lower angular cell data‖ ^ 2 := by
  have outer := WithLp.prod_norm_sq_eq_of_L2 data
  have bulk := WithLp.prod_norm_sq_eq_of_L2 data.ofLp.1
  have graphBoundary := WithLp.prod_norm_sq_eq_of_L2 data.ofLp.2
  have graphs := WithLp.prod_norm_sq_eq_of_L2 data.ofLp.2.ofLp.1
  have boundary := WithLp.prod_norm_sq_eq_of_L2 data.ofLp.2.ofLp.2
  change ‖data‖ ^ 2 = ‖data.ofLp.1‖ ^ 2 + ‖data.ofLp.2‖ ^ 2 at outer
  change ‖data.ofLp.1‖ ^ 2 = ‖data.ofLp.1.ofLp.1‖ ^ 2 +
    ‖data.ofLp.1.ofLp.2‖ ^ 2 at bulk
  change ‖data.ofLp.2‖ ^ 2 = ‖data.ofLp.2.ofLp.1‖ ^ 2 +
    ‖data.ofLp.2.ofLp.2‖ ^ 2 at graphBoundary
  change ‖data.ofLp.2.ofLp.1‖ ^ 2 = ‖data.ofLp.2.ofLp.1.ofLp.1‖ ^ 2 +
    ‖data.ofLp.2.ofLp.1.ofLp.2‖ ^ 2 at graphs
  change ‖data.ofLp.2.ofLp.2‖ ^ 2 = ‖data.ofLp.2.ofLp.2.ofLp.1‖ ^ 2 +
    ‖data.ofLp.2.ofLp.2.ofLp.2‖ ^ 2 at boundary
  simp only [highKnownWeightedProjection_apply, highKnownAuxiliaryProjection_apply,
    highKnownF0GraphProjection_apply, highKnownF2GraphProjection_apply,
    highKnownDatumProjection_apply, highKnownIncomingProjection_apply]
  linarith

section Bounds

variable (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell : ℕ)

theorem ActualHighKnownCarrier.norm_sq
    (data : ActualHighKnownCarrier parameters lower positive bounded angular cell) :
    ‖data‖ ^ 2 =
      ‖actualHighKnownWeighted parameters lower positive bounded angular cell data‖ ^ 2 +
      ‖actualHighKnownAuxiliary parameters lower positive bounded angular cell data‖ ^ 2 +
      ‖actualHighKnownF0Graph parameters lower positive bounded angular cell data‖ ^ 2 +
      ‖actualHighKnownF2Graph parameters lower positive bounded angular cell data‖ ^ 2 +
      ‖actualHighKnownDatum parameters lower positive bounded angular cell data‖ ^ 2 +
      ‖actualHighKnownIncoming parameters lower positive bounded angular cell data‖ ^ 2 := by
  exact actualHighKnownAmbient_norm_sq parameters lower angular cell data.val

/-- Every literal BF2 coordinate is bounded by the single carrier norm. -/
theorem ActualHighKnownCarrier.component_bounds
    (data : ActualHighKnownCarrier parameters lower positive bounded angular cell) :
    ‖actualHighKnownWeighted parameters lower positive bounded angular cell data‖ ≤ ‖data‖ ∧
    ‖actualHighKnownAuxiliary parameters lower positive bounded angular cell data‖ ≤ ‖data‖ ∧
    ‖actualHighKnownF0Graph parameters lower positive bounded angular cell data‖ ≤ ‖data‖ ∧
    ‖actualHighKnownF2Graph parameters lower positive bounded angular cell data‖ ≤ ‖data‖ ∧
      ‖actualHighKnownDatum parameters lower positive bounded angular cell data‖ ≤ ‖data‖ ∧
    ‖actualHighKnownIncoming parameters lower positive bounded angular cell data‖ ≤ ‖data‖ := by
  have square := ActualHighKnownCarrier.norm_sq parameters lower positive bounded angular cell data
  have w0 := sq_nonneg ‖actualHighKnownWeighted parameters lower positive bounded angular cell data‖
  have w1 := sq_nonneg ‖actualHighKnownAuxiliary parameters lower positive bounded angular cell data‖
  have w2 := sq_nonneg ‖actualHighKnownF0Graph parameters lower positive bounded angular cell data‖
  have w3 := sq_nonneg ‖actualHighKnownF2Graph parameters lower positive bounded angular cell data‖
  have w4 := sq_nonneg ‖actualHighKnownDatum parameters lower positive bounded angular cell data‖
  have w5 := sq_nonneg ‖actualHighKnownIncoming parameters lower positive bounded angular cell data‖
  have n0 := norm_nonneg data
  have n1 := norm_nonneg (actualHighKnownWeighted parameters lower positive bounded angular cell data)
  have n2 := norm_nonneg (actualHighKnownAuxiliary parameters lower positive bounded angular cell data)
  have n3 := norm_nonneg (actualHighKnownF0Graph parameters lower positive bounded angular cell data)
  have n4 := norm_nonneg (actualHighKnownF2Graph parameters lower positive bounded angular cell data)
  have n5 := norm_nonneg (actualHighKnownDatum parameters lower positive bounded angular cell data)
  have n6 := norm_nonneg (actualHighKnownIncoming parameters lower positive bounded angular cell data)
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem ActualHighKnownCarrier.graph_sum_bound
    (data : ActualHighKnownCarrier parameters lower positive bounded angular cell) :
    2 * ‖actualHighKnownF0Graph parameters lower positive bounded angular cell data‖ +
      ‖actualHighKnownF2Graph parameters lower positive bounded angular cell data‖ ≤
        3 * ‖data‖ := by
  have square := ActualHighKnownCarrier.norm_sq parameters lower positive bounded angular cell data
  have first : ‖actualHighKnownF0Graph parameters lower positive bounded angular cell data‖ ≤
      ‖data‖ := by
    nlinarith [sq_nonneg ‖actualHighKnownWeighted parameters lower positive bounded angular cell data‖,
      sq_nonneg ‖actualHighKnownAuxiliary parameters lower positive bounded angular cell data‖,
      sq_nonneg ‖actualHighKnownF2Graph parameters lower positive bounded angular cell data‖,
      sq_nonneg ‖actualHighKnownDatum parameters lower positive bounded angular cell data‖,
      sq_nonneg ‖actualHighKnownIncoming parameters lower positive bounded angular cell data‖,
      norm_nonneg data,
      norm_nonneg (actualHighKnownF0Graph parameters lower positive bounded angular cell data)]
  have second : ‖actualHighKnownF2Graph parameters lower positive bounded angular cell data‖ ≤
      ‖data‖ := by
    nlinarith [sq_nonneg ‖actualHighKnownWeighted parameters lower positive bounded angular cell data‖,
      sq_nonneg ‖actualHighKnownAuxiliary parameters lower positive bounded angular cell data‖,
      sq_nonneg ‖actualHighKnownF0Graph parameters lower positive bounded angular cell data‖,
      sq_nonneg ‖actualHighKnownDatum parameters lower positive bounded angular cell data‖,
      sq_nonneg ‖actualHighKnownIncoming parameters lower positive bounded angular cell data‖,
      norm_nonneg data,
      norm_nonneg (actualHighKnownF2Graph parameters lower positive bounded angular cell data)]
  nlinarith

end Bounds

end Grad.AnnularCurrentSource
