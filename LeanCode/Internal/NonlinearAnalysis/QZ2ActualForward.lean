import QZ1StateDirections

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

open scoped ContDiff

namespace Grad.SmoothForward

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges
open Grad.Q24Realization Grad.NonlinearQuotientBounds Grad.QuotientProjection

/-- The literal smooth-core state derivative of Q21, including its actual
N18 reference transfer. Curvature and seed are fixed, not differentiated. -/
def literalSmoothForwardRows (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (direction : stateSmoothRange parameters reference insideR) : QuotientRows parameters :=
  fixedSliceDerivative parameters cellLength reference insideR seed insideS 1
    (realJointCoreToJoint parameters reference insideR base)
    (fun _ => realJointCoreToJoint parameters reference insideR (0, direction))

/-- COR29's actual real continuous linear forward operator at a smooth
state, with unchanged loss six. Its derivative is constructed above, not
assumed as an interface premise. -/
def actualSmoothForward (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 4 ≤ grade) (base : RealJointCore parameters reference insideR) :
    stateRange parameters reference insideR (grade + 6) (realHighLarge grade) →L[ℝ]
      sourceRange parameters grade (forwardLarge large) :=
  (fderiv ℝ (completedRealFixedSlice parameters cellLength reference insideR seed insideS grade (forwardLarge large))
    (realJointCoreEmbed parameters reference insideR (grade + 6) (realHighLarge grade) base)).comp
    (stateDirection parameters reference insideR (grade + 6) (realHighLarge grade))

theorem actualSmoothForward_core (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 4 ≤ grade) (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (direction : stateSmoothRange parameters reference insideR) :
    sourceInclusion parameters grade (forwardLarge large)
      (actualSmoothForward parameters cellLength reference insideR seed insideS grade large base
        (stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) direction)) =
      quotientEta parameters grade (literalSmoothForwardRows parameters cellLength reference insideR seed insideS base direction) := by
  have identity := completedRealFixedSlice_derivative_core parameters cellLength reference insideR seed insideS
    grade (forwardLarge large) 1 base axis (fun _ => (0, direction))
  rw [iteratedFDeriv_one_apply] at identity
  exact identity

theorem literalSmoothForwardRows_mem (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (direction : stateSmoothRange parameters reference insideR) :
    literalSmoothForwardRows parameters cellLength reference insideR seed insideS base direction ∈
      sourceSmoothRange parameters :=
  fixedSliceDerivative_constrained_mem parameters cellLength reference insideR seed insideS 1 base axis
    (fun _ => (0, direction))

theorem actualSmoothForward_unique (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 4 ≤ grade) (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (other : stateRange parameters reference insideR (grade + 6) (realHighLarge grade) →L[ℝ]
      sourceRange parameters grade (forwardLarge large))
    (core : ∀ direction, sourceInclusion parameters grade (forwardLarge large)
      (other (stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) direction)) =
      quotientEta parameters grade (literalSmoothForwardRows parameters cellLength reference insideR seed insideS base direction)) :
    other = actualSmoothForward parameters cellLength reference insideR seed insideS grade large base := by
  apply ContinuousLinearMap.ext
  exact isClosed_property (stateSmoothEmbedding_denseRange parameters reference insideR (grade + 6) (realHighLarge grade))
    (isClosed_eq other.continuous (actualSmoothForward parameters cellLength reference insideR seed insideS grade large base).continuous)
    (fun direction => Subtype.ext ((core direction).trans
      (actualSmoothForward_core parameters cellLength reference insideR seed insideS grade large base axis direction).symm))

end Grad.SmoothForward
