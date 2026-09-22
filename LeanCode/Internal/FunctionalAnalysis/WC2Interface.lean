import WeakPullbackProof
import MixingNorm
import OC1RowOrthogonality
import OC2CoefficientComposition

noncomputable section

open Grad.PDEBootstrap Grad.KernelPullback

namespace Grad.WeakPullback.H1

def pulledDerivative (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldH1)
    (output : Fin 2) : FieldL2 :=
  ∑ input : Fin 2, orthogonal (spatialDirection output) input •
    orthogonalPullback orthogonal (weakDerivative input field)

def WeakCoordinatesGoal : Prop :=
  ∀ (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldH1) (output : Fin 2),
    distributionDerivative output
        (distributionEmbedding (orthogonalPullback orthogonal (valueInclusion field))) =
      distributionEmbedding (pulledDerivative orthogonal field output)

def NormSqGoal : Prop :=
  ∀ (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldH1),
    ‖orthogonalPullback orthogonal (valueInclusion field)‖ ^ 2 +
      ∑ output : Fin 2, ‖pulledDerivative orthogonal field output‖ ^ 2 = ‖field‖ ^ 2

def PullbackGoal : Prop :=
  ∃ h1Pullback : (Spatial ≃ₗᵢ[ℝ] Spatial) → (FieldH1 ≃ₗᵢ[ℂ] FieldH1),
    (∀ orthogonal field,
      valueInclusion (h1Pullback orthogonal field) =
        orthogonalPullback orthogonal (valueInclusion field)) ∧
    (∀ orthogonal field output,
      weakDerivative output (h1Pullback orthogonal field) = pulledDerivative orthogonal field output) ∧
    (∀ orthogonal field, ‖h1Pullback orthogonal field‖ = ‖field‖) ∧
    (∀ orthogonal, (h1Pullback orthogonal).symm = h1Pullback orthogonal.symm)

theorem interfaceConsumer (goal : PullbackGoal) :
    ∃ h1Pullback : (Spatial ≃ₗᵢ[ℝ] Spatial) → (FieldH1 ≃ₗᵢ[ℂ] FieldH1),
      (∀ (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldH1),
        valueInclusion (h1Pullback orthogonal field) =
          orthogonalPullback orthogonal (valueInclusion field)) ∧
      (∀ (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldH1) (output : Fin 2),
        weakDerivative output (h1Pullback orthogonal field) =
          ∑ input : Fin 2, orthogonal (spatialDirection output) input •
            orthogonalPullback orthogonal (weakDerivative input field)) ∧
      (∀ (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldH1),
        ‖h1Pullback orthogonal field‖ = ‖field‖) ∧
      (∀ (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial),
        (h1Pullback orthogonal).symm = h1Pullback orthogonal.symm) := goal

end Grad.WeakPullback.H1
