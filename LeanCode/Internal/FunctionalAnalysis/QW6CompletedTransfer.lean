import QW5CoreGoal
import QT8Consumer

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.ConstrainedTransfer

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.SmoothingFamily

theorem denseIsometryExtension_core {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (mapping : E →L[ℝ] G) (embedding : E →ₗᵢ[ℝ] F) (dense : DenseRange embedding) (field : E) :
    mapping.extend embedding.toContinuousLinearMap (embedding field) = mapping field :=
  ContinuousLinearMap.extend_eq mapping dense embedding.isometry.isUniformInducing field

theorem stateGradeEmbedding_tagged (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (field : stateSmoothRange parameters parameter inside) :
    stateGradeEmbedding parameters parameter inside grade large
      (⟨field⟩ : StateGradeCore parameters parameter inside grade large) =
        stateSmoothEmbedding parameters parameter inside grade large field := rfl

def gradeCoreTransferLinear (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    StateGradeCore parameters first insideFirst grade large →ₗ[ℝ]
      stateRange parameters second insideSecond grade large :=
  (stateSmoothEmbedding parameters second insideSecond grade large).comp
    ((constrainedCoreTransfer parameters first insideFirst second insideSecond).comp NormedCoreCopy.toCoreLinear)

def gradeCoreTransferContinuous (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    StateGradeCore parameters first insideFirst grade large →L[ℝ]
      stateRange parameters second insideSecond grade large :=
  (gradeCoreTransferLinear parameters first insideFirst second insideSecond grade large).mkContinuous
    (transferConstant parameters first second grade) (fun field =>
      coreTransfer_norm_le parameters first insideFirst second insideSecond grade field.toCore.val)

theorem gradeCoreTransferContinuous_tagged (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (field : stateSmoothRange parameters first insideFirst) :
    gradeCoreTransferContinuous parameters first insideFirst second insideSecond grade large
      (⟨field⟩ : StateGradeCore parameters first insideFirst grade large) =
        stateSmoothEmbedding parameters second insideSecond grade large
          (constrainedCoreTransfer parameters first insideFirst second insideSecond field) := rfl

/-- Extend the actual N18 core map along the accepted dense isometric
embedding into the canonical complete real target range. -/
def completedTransfer (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    stateRange parameters first insideFirst grade large →L[ℝ]
      stateRange parameters second insideSecond grade large :=
  (gradeCoreTransferContinuous parameters first insideFirst second insideSecond grade large).extend
    (stateGradeEmbedding parameters first insideFirst grade large).toContinuousLinearMap

theorem completedTransfer_core (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (field : stateSmoothRange parameters first insideFirst) :
    completedTransfer parameters first insideFirst second insideSecond grade large
      (stateSmoothEmbedding parameters first insideFirst grade large field) =
        stateSmoothEmbedding parameters second insideSecond grade large
          (constrainedCoreTransfer parameters first insideFirst second insideSecond field) := by
  have equality := denseIsometryExtension_core
    (gradeCoreTransferContinuous parameters first insideFirst second insideSecond grade large)
    (stateGradeEmbedding parameters first insideFirst grade large)
    (stateGradeEmbedding_denseRange parameters first insideFirst grade large)
    (⟨field⟩ : StateGradeCore parameters first insideFirst grade large)
  rw [stateGradeEmbedding_tagged, gradeCoreTransferContinuous_tagged] at equality
  exact equality

theorem completedTransfer_bound (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (field : stateRange parameters first insideFirst grade large) :
    ‖completedTransfer parameters first insideFirst second insideSecond grade large field‖ ≤
      transferConstant parameters first second grade * ‖field‖ := by
  refine isClosed_property (stateSmoothEmbedding_denseRange parameters first insideFirst grade large)
    (isClosed_le (completedTransfer parameters first insideFirst second insideSecond grade large).continuous.norm
      (continuous_const.mul continuous_norm)) ?_ field
  intro core
  rw [completedTransfer_core]
  exact coreTransfer_norm_le parameters first insideFirst second insideSecond grade core.val

end Grad.ConstrainedTransfer
