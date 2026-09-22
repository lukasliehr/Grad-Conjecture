import QZ4CoreLinear

noncomputable section

namespace Grad.SmoothForward

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges
open Grad.Q24Realization Grad.NonlinearQuotientBounds

/-- COR29's actual smooth-core equation at the exact six-grade loss. The
core derivative and completed forward operator are explicit constructions. -/
def ForwardCoreGoal : Prop :=
  ∀ (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 4 ≤ grade) (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (direction : stateSmoothRange parameters reference insideR),
    actualSmoothForward parameters cellLength reference insideR seed insideS grade large base
      (stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) direction) =
    sourceSmoothEmbedding parameters grade (forwardLarge large)
      (literalSmoothForward parameters cellLength reference insideR seed insideS base axis direction)

/-- Original-norm operator estimate, uniform on the given low state ball.
The high state norm is unrestricted. Finite parameters are fixed here. -/
def ForwardBoundGoal : Prop :=
  ∀ (parameters : PhaseParameters) (cellLength epsilon : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 4 ≤ grade) (bound : ℝ),
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : stateSmoothRange parameters reference insideR),
      ChartAxisCondition (smoothingChartCore parameters base.val) →
      ‖stateSmoothEmbedding parameters reference insideR 4 realLowLarge base‖ ≤ bound →
      ‖actualSmoothForward parameters cellLength reference insideR seed insideS grade large (epsilon, base)‖ ≤
        constant * (2 + ‖stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) base‖)

def SmoothForwardGoal : Prop := ForwardCoreGoal ∧ ForwardBoundGoal

theorem literalSmoothForward_completedCLM : SmoothForwardGoal :=
  ⟨actualSmoothForward_core_value, actualSmoothForward_operator_bound⟩

end Grad.SmoothForward
