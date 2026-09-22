import QZ3ForwardBounds

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

namespace Grad.SmoothForward

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges
open Grad.Q24Realization Grad.NonlinearQuotientBounds

def literalSmoothForwardValue (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (direction : stateSmoothRange parameters reference insideR) : sourceSmoothRange parameters :=
  ⟨literalSmoothForwardRows parameters cellLength reference insideR seed insideS base direction,
    literalSmoothForwardRows_mem parameters cellLength reference insideR seed insideS base axis direction⟩

theorem actualSmoothForward_core_value (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 4 ≤ grade) (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (direction : stateSmoothRange parameters reference insideR) :
    actualSmoothForward parameters cellLength reference insideR seed insideS grade large base
      (stateSmoothEmbedding parameters reference insideR (grade + 6) (realHighLarge grade) direction) =
    sourceSmoothEmbedding parameters grade (forwardLarge large)
      (literalSmoothForwardValue parameters cellLength reference insideR seed insideS base axis direction) :=
  Subtype.ext (actualSmoothForward_core parameters cellLength reference insideR seed insideS grade large base axis direction)

/-- The actual smooth-core derivative is real linear into the identical
smooth real constrained source, proved using the exact faithful embeddings. -/
def literalSmoothForward (parameters : PhaseParameters) (cellLength : ℝ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val)) :
    stateSmoothRange parameters reference insideR →ₗ[ℝ] sourceSmoothRange parameters where
  toFun := literalSmoothForwardValue parameters cellLength reference insideR seed insideS base axis
  map_add' first second := by
    apply sourceSmoothEmbedding_injective parameters 4 (forwardLarge (le_refl 4))
    simp only [map_add, ← actualSmoothForward_core_value parameters cellLength reference insideR seed insideS
      4 (le_refl 4) base axis]
  map_smul' scalar direction := by
    apply sourceSmoothEmbedding_injective parameters 4 (forwardLarge (le_refl 4))
    simp only [map_smul, ← actualSmoothForward_core_value parameters cellLength reference insideR seed insideS
      4 (le_refl 4) base axis]
    rfl

end Grad.SmoothForward
