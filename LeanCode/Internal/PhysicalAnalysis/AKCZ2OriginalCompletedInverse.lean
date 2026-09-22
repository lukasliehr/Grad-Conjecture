import AKCZ1ExactCoreResolvent

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
namespace Grad.NashMoser.InverseCalculus
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades

variable (parameters : PhaseParameters) (reference : Seed.Parameters) (inside : reference ∈ Seed.parameterDomain)
    (sourceGrade outputGrade : ℕ) (sourceLarge : 3 ≤ sourceGrade) (outputLarge : 3 ≤ outputGrade)
    (inverse : sourceSmoothRange parameters →ₗ[ℝ] stateSmoothRange parameters reference inside)
    (constant : ℝ)
    (bounded : ∀ source, ‖stateSmoothEmbedding parameters reference inside outputGrade outputLarge (inverse source)‖ ≤
      constant*‖sourceSmoothEmbedding parameters sourceGrade sourceLarge source‖)

/-- The SAME original inverse on the source normed core, at its actual
source/output grades. No same-grade inverse structure is introduced. -/
def inverseOnSourceGradeCore : SourceGradeCore parameters sourceGrade sourceLarge →L[ℝ]
    stateRange parameters reference inside outputGrade outputLarge :=
  (((stateSmoothEmbedding parameters reference inside outputGrade outputLarge).comp inverse).comp
    NormedCoreCopy.toCoreLinear).mkContinuous constant (by
      intro source
      rw [NormedCoreCopy.norm_eq]
      change ‖stateSmoothEmbedding parameters reference inside outputGrade outputLarge (inverse source.toCore)‖ ≤
        constant*‖sourceSmoothEmbedding parameters sourceGrade sourceLarge source.toCore‖
      exact bounded source.toCore)

/-- Unique bounded extension to the original real completed source grade. -/
def completedOriginalInverse : sourceRange parameters sourceGrade sourceLarge →L[ℝ]
    stateRange parameters reference inside outputGrade outputLarge :=
  (inverseOnSourceGradeCore parameters reference inside sourceGrade outputGrade sourceLarge outputLarge inverse constant bounded).extend
    (sourceGradeEmbedding parameters sourceGrade sourceLarge).toContinuousLinearMap

theorem completedOriginalInverse_core (source : sourceSmoothRange parameters) :
    completedOriginalInverse parameters reference inside sourceGrade outputGrade sourceLarge outputLarge inverse constant bounded
      (sourceSmoothEmbedding parameters sourceGrade sourceLarge source) =
    stateSmoothEmbedding parameters reference inside outputGrade outputLarge (inverse source) := by
  exact Grad.ConstrainedTransfer.denseIsometryExtension_core
    (inverseOnSourceGradeCore parameters reference inside sourceGrade outputGrade sourceLarge outputLarge inverse constant bounded)
    (sourceGradeEmbedding parameters sourceGrade sourceLarge)
    (sourceGradeEmbedding_denseRange parameters sourceGrade sourceLarge)
    (⟨source⟩ : SourceGradeCore parameters sourceGrade sourceLarge)

theorem completedOriginalInverse_bound (source : sourceRange parameters sourceGrade sourceLarge) :
    ‖completedOriginalInverse parameters reference inside sourceGrade outputGrade sourceLarge outputLarge inverse constant bounded source‖ ≤
      constant*‖source‖ := by
  apply isClosed_property (sourceSmoothEmbedding_denseRange parameters sourceGrade sourceLarge)
    (isClosed_le (completedOriginalInverse parameters reference inside sourceGrade outputGrade sourceLarge outputLarge inverse constant bounded).continuous.norm
      (continuous_const.mul continuous_norm)) _ source
  intro core
  rw [completedOriginalInverse_core]
  exact bounded core

theorem completedOriginalInverse_unique
    (other : sourceRange parameters sourceGrade sourceLarge →L[ℝ] stateRange parameters reference inside outputGrade outputLarge)
    (same : ∀ source : sourceSmoothRange parameters, other (sourceSmoothEmbedding parameters sourceGrade sourceLarge source) =
      stateSmoothEmbedding parameters reference inside outputGrade outputLarge (inverse source)) :
    other = completedOriginalInverse parameters reference inside sourceGrade outputGrade sourceLarge outputLarge inverse constant bounded := by
  apply ContinuousLinearMap.ext
  exact congrFun ((sourceSmoothEmbedding_denseRange parameters sourceGrade sourceLarge).equalizer
    other.continuous
    (completedOriginalInverse parameters reference inside sourceGrade outputGrade sourceLarge outputLarge inverse constant bounded).continuous
    (funext fun source => (same source).trans (completedOriginalInverse_core parameters reference inside sourceGrade outputGrade
      sourceLarge outputLarge inverse constant bounded source).symm))

end Grad.NashMoser.InverseCalculus
