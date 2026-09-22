import QX7RawDerivative

noncomputable section

namespace Grad.RawForward

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.Q24Realization Grad.RealFixedRanges Grad.ConstrainedGrades Grad.SmoothForward
open Grad.QuotientProjection

def ForwardGradeCompatibilityGoal : Prop :=
  ∀ (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (lower upper : ℕ) (large : 4 ≤ lower) (ordered : lower ≤ upper)
    (base : RealJointCore parameters reference insideR),
    ChartAxisCondition (smoothingChartCore parameters base.2.val) →
    (sourceLowering parameters (forwardLarge large) ordered).comp
      (actualSmoothForward parameters cellLength reference insideR seed insideS upper (large.trans ordered) base) =
    (actualSmoothForward parameters cellLength reference insideR seed insideS lower large base).comp
      (stateLowering parameters reference insideR (realHighLarge lower) (Nat.add_le_add_right ordered 6))

def ForwardRawIdentityGoal : Prop :=
  ∀ (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (direction : stateSmoothRange parameters reference insideR),
    HasDerivAt
      (fun scalar : ℝ => quotientEta parameters grade
        (rawFixedSliceCore parameters cellLength reference insideR seed insideS
          (base.1, base.2 + scalar • direction)))
      (quotientEta parameters grade (rawReconstructionCore parameters
        (literalSmoothForward parameters cellLength reference insideR seed insideS base axis direction).val)) 0

/-- COR30: the exact forward core law, canonical grade compatibility and
the actual differentiated raw-equation reconstruction, with no assumed inverse. -/
def LiteralForwardCompatibilityGoal : Prop :=
  ForwardCoreGoal ∧ ForwardGradeCompatibilityGoal ∧ ForwardRawIdentityGoal

theorem literalForward_coreLaw_and_gradeCompatibility : LiteralForwardCompatibilityGoal := by
  refine ⟨literalSmoothForward_completedCLM.1, ?_, literalSmoothForward_rawDerivative⟩
  intro parameters cellLength reference insideR seed insideS lower upper large ordered base axis
  exact actualSmoothForward_gradeCompatibility parameters cellLength reference insideR seed insideS large ordered base axis

/-- Immediate smooth-core consumer of the completed operator: its named
core value is exactly the raw derivative after the literal reconstruction. -/
theorem actualForward_raw_core_consumer (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 4 ≤ grade) (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (direction : stateSmoothRange parameters reference insideR) :
    ∃ coreValue : sourceSmoothRange parameters,
      actualSmoothForward parameters cellLength reference insideR seed insideS grade large base
        (stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) direction) =
        sourceSmoothEmbedding parameters grade (forwardLarge large) coreValue ∧
      HasDerivAt
        (fun scalar : ℝ => quotientEta parameters grade
          (rawFixedSliceCore parameters cellLength reference insideR seed insideS
            (base.1, base.2 + scalar • direction)))
        (quotientEta parameters grade (rawReconstructionCore parameters coreValue.val)) 0 :=
  ⟨literalSmoothForward parameters cellLength reference insideR seed insideS base axis direction,
    literalSmoothForward_completedCLM.1 parameters cellLength reference insideR seed insideS grade large base axis direction,
    literalSmoothForward_rawDerivative parameters cellLength reference insideR seed insideS grade base axis direction⟩

end Grad.RawForward
