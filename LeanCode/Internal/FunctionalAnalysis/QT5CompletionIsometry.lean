import QT4NormedCore
import Mathlib.Analysis.Normed.Module.Completion

noncomputable section

namespace Grad.RealFixedRanges

section Completion

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def completionMap (embedding : E →ₗᵢ[ℝ] F) : UniformSpace.Completion E →L[ℝ] F :=
  embedding.toContinuousLinearMap.extend
    (UniformSpace.Completion.toComplₗᵢ : E →ₗᵢ[ℝ] UniformSpace.Completion E).toContinuousLinearMap

theorem completionMap_eta (embedding : E →ₗᵢ[ℝ] F) (field : E) :
    completionMap embedding
      ((UniformSpace.Completion.toComplₗᵢ : E →ₗᵢ[ℝ] UniformSpace.Completion E) field) = embedding field := by
  exact ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.toComplₗᵢ : E →ₗᵢ[ℝ] UniformSpace.Completion E).isometry.isUniformInducing field

theorem completionMap_norm (embedding : E →ₗᵢ[ℝ] F) (field : UniformSpace.Completion E) :
    ‖completionMap embedding field‖ = ‖field‖ := by
  have dense : DenseRange (UniformSpace.Completion.toComplₗᵢ : E →ₗᵢ[ℝ] UniformSpace.Completion E) :=
    UniformSpace.Completion.denseRange_coe
  refine isClosed_property dense
    (isClosed_eq (completionMap embedding).continuous.norm continuous_norm) ?_ field
  intro core
  rw [completionMap_eta, embedding.norm_map,
    (UniformSpace.Completion.toComplₗᵢ : E →ₗᵢ[ℝ] UniformSpace.Completion E).norm_map]

def completionIsometry (embedding : E →ₗᵢ[ℝ] F) : UniformSpace.Completion E →ₗᵢ[ℝ] F :=
  { (completionMap embedding).toLinearMap with norm_map' := completionMap_norm embedding }

theorem completionIsometry_denseRange (embedding : E →ₗᵢ[ℝ] F) (dense : DenseRange embedding) :
    DenseRange (completionIsometry embedding) := by
  apply dense.mono
  rintro _ ⟨field, rfl⟩
  exact ⟨(UniformSpace.Completion.toComplₗᵢ : E →ₗᵢ[ℝ] UniformSpace.Completion E) field,
    completionMap_eta embedding field⟩

theorem completionIsometry_surjective (embedding : E →ₗᵢ[ℝ] F) (dense : DenseRange embedding) :
    Function.Surjective (completionIsometry embedding) := by
  have closed := (completionIsometry embedding).isometry.isClosedEmbedding.isClosed_range
  intro point
  have member := completionIsometry_denseRange embedding dense point
  rw [closed.closure_eq] at member
  exact member

/-- The canonical norm-completion equivalence, with the specified dense
linear isometry as its exact restriction to the original normed core. -/
def completionEquiv (embedding : E →ₗᵢ[ℝ] F) (dense : DenseRange embedding) :
    UniformSpace.Completion E ≃ₗᵢ[ℝ] F :=
  LinearIsometryEquiv.ofSurjective (completionIsometry embedding)
    (completionIsometry_surjective embedding dense)

theorem completionEquiv_eta (embedding : E →ₗᵢ[ℝ] F) (dense : DenseRange embedding) (field : E) :
    completionEquiv embedding dense
      ((UniformSpace.Completion.toComplₗᵢ : E →ₗᵢ[ℝ] UniformSpace.Completion E) field) = embedding field :=
  completionMap_eta embedding field

end Completion

end Grad.RealFixedRanges
