import QZ5Goal

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

namespace Grad.SmoothForward

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.Q24Realization Grad.NonlinearQuotientBounds

/-- Exact dependency-ready forward operator for a later finite-loss
composition. No inverse or inverse identity is supplied as a premise. -/
theorem actualSmoothForward_exists (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 4 ≤ grade) (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val)) :
    ∃ forward : stateRange parameters reference insideR (grade + 6) (realHighLarge grade) →L[ℝ]
        sourceRange parameters grade (forwardLarge large),
      ∀ direction : stateSmoothRange parameters reference insideR,
        forward (stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) direction) =
          sourceSmoothEmbedding parameters grade (forwardLarge large)
            (literalSmoothForward parameters cellLength reference insideR seed insideS base axis direction) :=
  ⟨actualSmoothForward parameters cellLength reference insideR seed insideS grade large base,
    literalSmoothForward_completedCLM.1 parameters cellLength reference insideR seed insideS grade large base axis⟩

/-- Immediate grade-composition consumer. This proves the canonical
forward compatibility needed downstream, but does not claim COR30's
separate raw-equation reconstruction obligation. -/
theorem actualSmoothForward_gradeCompatibility {lower upper : ℕ}
    (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (large : 4 ≤ lower) (ordered : lower ≤ upper) (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val)) :
    (sourceLowering parameters (forwardLarge large) ordered).comp
      (actualSmoothForward parameters cellLength reference insideR seed insideS upper (large.trans ordered) base) =
    (actualSmoothForward parameters cellLength reference insideR seed insideS lower large base).comp
      (stateLowering parameters reference insideR (realHighLarge lower) (Nat.add_le_add_right ordered 6)) := by
  apply ContinuousLinearMap.ext
  apply isClosed_property
    (stateSmoothEmbedding_denseRange parameters reference insideR (upper + 6) (realHighLarge upper))
    (isClosed_eq
      ((sourceLowering parameters (forwardLarge large) ordered).continuous.comp
        (actualSmoothForward parameters cellLength reference insideR seed insideS upper (large.trans ordered) base).continuous)
      ((actualSmoothForward parameters cellLength reference insideR seed insideS lower large base).continuous.comp
        (stateLowering parameters reference insideR (realHighLarge lower) (Nat.add_le_add_right ordered 6)).continuous))
  intro direction
  change sourceLowering parameters (forwardLarge large) ordered
    (actualSmoothForward parameters cellLength reference insideR seed insideS upper (large.trans ordered) base
      (stateSmoothEmbedding parameters reference insideR (upper + 6) (realHighLarge upper) direction)) = _
  rw [actualSmoothForward_core_value parameters cellLength reference insideR seed insideS upper (large.trans ordered) base axis,
    sourceLowering_core, Function.comp_apply, stateLowering_core,
    actualSmoothForward_core_value parameters cellLength reference insideR seed insideS lower large base axis]

end Grad.SmoothForward
