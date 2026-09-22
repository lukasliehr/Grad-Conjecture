import WC2Proof

noncomputable section

open Grad.PDEBootstrap Grad.KernelPullback

namespace Grad.WeakPullback.H1

theorem namedConsumer :
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
      (h1Pullback orthogonal).symm = h1Pullback orthogonal.symm) :=
  ⟨valueInclusion_h1Pullback, weakDerivative_h1Pullback, h1Pullback_norm, h1Pullback_symm⟩

theorem literalConsumer :
    ∃ action : (Spatial ≃ₗᵢ[ℝ] Spatial) → (FieldH1 ≃ₗᵢ[ℂ] FieldH1),
      (∀ (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldH1),
        valueInclusion (action orthogonal field) =
          orthogonalPullback orthogonal (valueInclusion field)) ∧
      (∀ (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldH1) (output : Fin 2),
        weakDerivative output (action orthogonal field) =
          ∑ input : Fin 2, orthogonal (spatialDirection output) input •
            orthogonalPullback orthogonal (weakDerivative input field)) ∧
      (∀ (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldH1),
        ‖action orthogonal field‖ = ‖field‖) ∧
      (∀ (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial),
        (action orthogonal).symm = action orthogonal.symm) :=
  interfaceConsumer pullbackProof

#check (weakCoordinates : WeakCoordinatesGoal)
#check (normSq : NormSqGoal)
#check (pullbackProof : PullbackGoal)
#check (literalConsumer : PullbackGoal)
#check (h1Pullback : (Spatial ≃ₗᵢ[ℝ] Spatial) → (FieldH1 ≃ₗᵢ[ℂ] FieldH1))

end Grad.WeakPullback.H1
