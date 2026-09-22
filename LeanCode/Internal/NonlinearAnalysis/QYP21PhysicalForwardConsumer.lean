import QYP20PhysicalFixedBounds

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 600000

namespace Grad.PhysicalCoordinates

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges
open Grad.Q24Realization Grad.NonlinearQuotientBounds Grad.SmoothForward Grad.QuotientProjection

def literalPhysicalSmoothForwardValue (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (direction : stateSmoothRange parameters reference insideR) : sourceSmoothRange parameters :=
  ⟨literalPhysicalSmoothForwardRows parameters cellLength reference insideR seed insideS base direction,
    literalPhysicalSmoothForwardRows_mem parameters cellLength reference insideR seed insideS base axis direction⟩

theorem actualPhysicalSmoothForward_core_value (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 4 ≤ grade) (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (direction : stateSmoothRange parameters reference insideR) :
    actualPhysicalSmoothForward parameters cellLength reference insideR seed grade large base
      (stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) direction) =
    sourceSmoothEmbedding parameters grade (forwardLarge large)
      (literalPhysicalSmoothForwardValue parameters cellLength reference insideR seed insideS base axis direction) :=
  Subtype.ext (actualPhysicalSmoothForward_core parameters cellLength reference insideR seed insideS grade large base axis direction)

/-- The actual smooth-core derivative is real linear into the identical
smooth real constrained source, proved using the exact faithful embeddings. -/
def literalPhysicalSmoothForward (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val)) :
    stateSmoothRange parameters reference insideR →ₗ[ℝ] sourceSmoothRange parameters where
  toFun := literalPhysicalSmoothForwardValue parameters cellLength reference insideR seed insideS base axis
  map_add' first second := by
    apply sourceSmoothEmbedding_injective parameters 4 (forwardLarge (le_refl 4))
    simp only [map_add, ← actualPhysicalSmoothForward_core_value parameters cellLength reference insideR seed insideS
      4 (le_refl 4) base axis]
  map_smul' scalar direction := by
    apply sourceSmoothEmbedding_injective parameters 4 (forwardLarge (le_refl 4))
    simp only [map_smul, ← actualPhysicalSmoothForward_core_value parameters cellLength reference insideR seed insideS
      4 (le_refl 4) base axis]
    rfl

theorem actualPhysicalSmoothForward_unique (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 4 ≤ grade) (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (other : stateRange parameters reference insideR (grade + 6) (realHighLarge grade) →L[ℝ]
      sourceRange parameters grade (forwardLarge large))
    (core : ∀ direction, sourceInclusion parameters grade (forwardLarge large)
      (other (stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) direction)) =
      quotientEta parameters grade (literalPhysicalSmoothForwardRows parameters cellLength reference insideR seed insideS base direction)) :
    other = actualPhysicalSmoothForward parameters cellLength reference insideR seed grade large base := by
  apply ContinuousLinearMap.ext
  exact isClosed_property (stateSmoothEmbedding_denseRange parameters reference insideR (grade + 6) (realHighLarge grade))
    (isClosed_eq other.continuous (actualPhysicalSmoothForward parameters cellLength reference insideR seed grade large base).continuous)
    (fun direction => Subtype.ext ((core direction).trans
      (actualPhysicalSmoothForward_core parameters cellLength reference insideR seed insideS grade large base axis direction).symm))

def PhysicalForwardCoreGoal : Prop :=
  ∀ (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 4 ≤ grade) (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (direction : stateSmoothRange parameters reference insideR),
    actualPhysicalSmoothForward parameters cellLength reference insideR seed grade large base
      (stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) direction) =
    sourceSmoothEmbedding parameters grade (forwardLarge large)
      (literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis direction)

/-- Original-norm operator estimate, uniform on the given low state ball.
The high state norm is unrestricted. Finite parameters are fixed here. -/
def PhysicalForwardBoundGoal : Prop :=
  ∀ (parameters : PhaseParameters) (cellLength epsilon : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (_insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 4 ≤ grade) (bound : ℝ),
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : stateSmoothRange parameters reference insideR),
      ChartAxisCondition (smoothingChartCore parameters base.val) →
      ‖stateSmoothEmbedding parameters reference insideR 4 realLowLarge base‖ ≤ bound →
      ‖actualPhysicalSmoothForward parameters cellLength reference insideR seed grade large (epsilon, base)‖ ≤
        constant * (2 + ‖stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) base‖)

def PhysicalSmoothForwardGoal : Prop := PhysicalForwardCoreGoal ∧ PhysicalForwardBoundGoal

theorem literalPhysicalSmoothForward_completedCLM : PhysicalSmoothForwardGoal :=
  ⟨actualPhysicalSmoothForward_core_value, actualPhysicalSmoothForward_operator_bound⟩

theorem actualPhysicalSmoothForward_exists (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 4 ≤ grade) (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val)) :
    ∃ forward : stateRange parameters reference insideR (grade + 6) (realHighLarge grade) →L[ℝ]
        sourceRange parameters grade (forwardLarge large),
      ∀ direction : stateSmoothRange parameters reference insideR,
        forward (stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) direction) =
          sourceSmoothEmbedding parameters grade (forwardLarge large)
            (literalPhysicalSmoothForward parameters cellLength reference insideR seed insideS base axis direction) :=
  ⟨actualPhysicalSmoothForward parameters cellLength reference insideR seed grade large base,
    literalPhysicalSmoothForward_completedCLM.1 parameters cellLength reference insideR seed insideS grade large base axis⟩


end Grad.PhysicalCoordinates
