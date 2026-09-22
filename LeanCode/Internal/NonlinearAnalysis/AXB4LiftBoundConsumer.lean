import AXB3AxisLiftBound

noncomputable section

namespace Grad.ChartAxisLift

open Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.Q24Realization

/-- Exact public AL27 contract on the already constructed actual AL15 lift.
The output norm is the literal original `X^q` completion norm; the datum norm
is `|d|_q`, hence contains exactly `T^(q+1)`, and the seed constant is uniform
on each compact admissible patch. -/
def AxisLiftBoundGoal : Prop :=
  ∀ (parameters : PhaseParameters) (radius : ℝ), ∀ (positive : 0 < radius),
    ∀ (_bounded : radius ≤ 1),
    ∀ grade : ℕ, 3 ≤ grade →
    ∀ seedPatch : Set Seed.Parameters, IsCompact seedPatch →
      seedPatch ⊆ Seed.parameterDomain →
      ∃ constant : ℝ, 0 ≤ constant ∧
        ∀ seed ∈ seedPatch, ∀ (inside : seed ∈ Seed.parameterDomain)
          (base : ChartState parameters) (_realBase : RealTangent base.1)
          (_axis : ChartAxisCondition base) (data : AxisData parameters)
          (_real : RealAxisData data),
          PhysicalAxisLiftRealization parameters radius positive seed inside base data ∧
            ‖Grad.SmoothingFamily.stateToGrade parameters grade
                (axisDataCapLiftLinear parameters radius positive seed inside base.1 data)‖ ≤
              constant * (axisDataNorm parameters grade data +
                (1 + tangentNorm (grade + 1) base.1) * axisDataNorm parameters 0 data)

theorem actual_axis_lift_bound : AxisLiftBoundGoal := by
  intro parameters radius positive bounded grade gradeMin seedPatch compact insidePatch
  exact actualPhysicalAxisLift_bound_on_patch (parameters := parameters)
    radius positive bounded grade gradeMin seedPatch compact insidePatch

end Grad.ChartAxisLift
