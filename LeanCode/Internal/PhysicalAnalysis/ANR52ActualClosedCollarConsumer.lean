import ANR51LiteralRadialEquation

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.WeightedTrace

private theorem robin_cancel (value : ComplexEuclidean 1) :
    -(2 : ℝ) • value + (2 : ℝ) • value = 0 := by rw [neg_smul, neg_add_cancel]

/-- AN19/V4 consumer: every high radial coefficient of the constructed
inverse of an original smooth source has its actual closed-collar smooth
representative, solves the literal second-order equation, and satisfies
the literal Robin row. No solution regularity or boundary derivative is a premise. -/
theorem actualClosedCollarAN19 (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1)
    (same : source.val = closedL2Core core) (mode : ℤ) (high : mode ∉ lowAngularModes) :
    let value := radialSectionExtension 1 lower bounded.le
      (diskRadialValueSection lower positive bounded mode (highRobinWeakInverse parameter source).val)
    (∀ᵐ radius ∂volume.restrict (Icc lower 1), value radius =
      diskRadialValue lower positive bounded.le mode (highRobinWeakInverse parameter source).val radius) ∧
    ContDiffOn ℝ ∞ value (Icc lower 1) ∧
    (∀ radius ∈ Icc lower 1,
      -derivWithin (derivWithin value (Icc lower 1)) (Icc lower 1) radius -
        radius⁻¹ • derivWithin value (Icc lower 1) radius +
        ((mode : ℝ) ^ 2 / radius ^ 2) • value radius +
        (((parameter ^ 2 * (1 - 4 / (mode : ℝ) ^ 2) : ℝ)) : ℂ) • value radius =
          diskCoreRadialCurve mode core radius) ∧
    derivWithin value (Icc lower 1) 1 + (2 : ℝ) • value 1 = 0 := by
  refine ⟨diskRadialValueSection_ae lower positive bounded mode _,
    weakInverse_closedCollar_smooth lower positive bounded mode high parameter source core same,
    (fun radius inside => weakInverse_literal_radialEquation lower positive bounded parameter source mode high core same radius inside), ?_⟩
  have robin := weakInverse_literal_robin lower positive bounded parameter source mode high
  have derivativeLaw := robin.derivWithin (uniqueDiffOn_Icc bounded 1 ⟨bounded.le, le_rfl⟩)
  exact (congrArg (fun derivative : ComplexEuclidean 1 => derivative + (2 : ℝ) •
    radialSectionExtension 1 lower bounded.le
      (diskRadialValueSection lower positive bounded mode (highRobinWeakInverse parameter source).val) 1) derivativeLaw).trans
        (robin_cancel _)

end Grad.CircularHighRegularity
