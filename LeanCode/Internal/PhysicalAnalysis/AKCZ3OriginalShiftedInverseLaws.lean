import AKCZ2OriginalCompletedInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000
namespace Grad.NashMoser.InverseCalculus
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.Q24Realization Grad.PhysicalCoordinates Grad.NonlinearQuotientBounds
open Grad.SmoothForward

variable (parameters : PhaseParameters) (cellLength : ℝ) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (inverse : sourceSmoothRange parameters →ₗ[ℝ] stateSmoothRange parameters reference insideR)

/-- The completed right inverse law is the correctly shifted inclusion:
A at grade s consumes V with output s+6. -/
theorem completedOriginalInverse_right
    (right : ∀ source, literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis (inverse source)=source)
    (grade : ℕ) (large : 4 ≤ grade) (inputGrade : ℕ) (ordered : grade ≤ inputGrade)
    (constant : ℝ)
    (bounded : ∀ source, ‖stateSmoothEmbedding parameters reference insideR (grade+6) (realHighLarge grade) (inverse source)‖ ≤
      constant*‖sourceSmoothEmbedding parameters inputGrade ((forwardLarge large).trans ordered) source‖)
    (source : sourceRange parameters inputGrade ((forwardLarge large).trans ordered)) :
    actualPhysicalSmoothForward parameters cellLength reference insideR seed grade large base
      (completedOriginalInverse parameters reference insideR inputGrade (grade+6)
        ((forwardLarge large).trans ordered) (realHighLarge grade) inverse constant bounded source) =
    sourceLowering parameters (forwardLarge large) ordered source := by
  apply isClosed_property (sourceSmoothEmbedding_denseRange parameters inputGrade ((forwardLarge large).trans ordered))
    (isClosed_eq ((actualPhysicalSmoothForward parameters cellLength reference insideR seed grade large base).continuous.comp
      (completedOriginalInverse parameters reference insideR inputGrade (grade+6) ((forwardLarge large).trans ordered)
        (realHighLarge grade) inverse constant bounded).continuous)
      (sourceLowering parameters (forwardLarge large) ordered).continuous) _ source
  intro core
  simp only [Function.comp_apply]
  rw [completedOriginalInverse_core,
    literalPhysicalSmoothForward_completedCLM.1 parameters cellLength reference insideR seed insideS grade large base axis,
    right,sourceLowering_core]

/-- The completed left inverse law also carries its actual shift:
V with source grade t consumes A at grade t on states of grade t+6. -/
theorem completedOriginalInverse_left
    (left : ∀ state, inverse (literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis state)=state)
    (sourceGrade : ℕ) (sourceLarge : 4 ≤ sourceGrade)
    (outputGrade : ℕ) (outputLarge : 3 ≤ outputGrade) (ordered : outputGrade ≤ sourceGrade+6)
    (constant : ℝ)
    (bounded : ∀ source, ‖stateSmoothEmbedding parameters reference insideR outputGrade outputLarge (inverse source)‖ ≤
      constant*‖sourceSmoothEmbedding parameters sourceGrade (forwardLarge sourceLarge) source‖)
    (state : stateRange parameters reference insideR (sourceGrade+6) (realHighLarge sourceGrade)) :
    completedOriginalInverse parameters reference insideR sourceGrade outputGrade
      (forwardLarge sourceLarge) outputLarge inverse constant bounded
      (actualPhysicalSmoothForward parameters cellLength reference insideR seed sourceGrade sourceLarge base state) =
    stateLowering parameters reference insideR outputLarge ordered state := by
  apply isClosed_property (stateSmoothEmbedding_denseRange parameters reference insideR (sourceGrade+6) (realHighLarge sourceGrade))
    (isClosed_eq ((completedOriginalInverse parameters reference insideR sourceGrade outputGrade (forwardLarge sourceLarge)
      outputLarge inverse constant bounded).continuous.comp
      (actualPhysicalSmoothForward parameters cellLength reference insideR seed sourceGrade sourceLarge base).continuous)
      (stateLowering parameters reference insideR outputLarge ordered).continuous) _ state
  intro core
  simp only [Function.comp_apply]
  rw [literalPhysicalSmoothForward_completedCLM.1 parameters cellLength reference insideR seed insideS sourceGrade sourceLarge base axis,
    completedOriginalInverse_core,left,stateLowering_core]

end Grad.NashMoser.InverseCalculus
