import WC2Interface

noncomputable section

open LineDeriv Grad.PDEBootstrap Grad.KernelPullback

namespace Grad.WeakPullback.H1

theorem weakCoordinates : WeakCoordinatesGoal := by
  intro orthogonal field output
  change lineDerivOp (spatialDirection output)
      (distributionEmbedding (orthogonalPullback orthogonal (valueInclusion field))) = _
  rw [embedding, directional]
  have expansion :
      lineDerivOp (orthogonal (spatialDirection output))
          (distributionEmbedding (valueInclusion field)) =
        ∑ input : Fin 2, orthogonal (spatialDirection output) input •
          lineDerivOp (spatialDirection input) (distributionEmbedding (valueInclusion field)) := by
    calc
      _ = lineDerivOp
          (∑ input : Fin 2, orthogonal (spatialDirection output) input • spatialDirection input)
          (distributionEmbedding (valueInclusion field)) :=
        congrArg (fun direction : Spatial =>
          lineDerivOp direction (distributionEmbedding (valueInclusion field)))
            (OrthogonalCoefficients.Composition.spatialDirection_expansion _)
      _ = ∑ input : Fin 2,
          lineDerivOp (orthogonal (spatialDirection output) input • spatialDirection input)
            (distributionEmbedding (valueInclusion field)) := lineDerivOp_left_sum _ _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro input membership
        exact lineDerivOp_left_smul _ _ _
  rw [expansion, map_sum]
  unfold pulledDerivative
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro input membership
  calc
    distributionPullback orthogonal
        (orthogonal (spatialDirection output) input •
          lineDerivOp (spatialDirection input) (distributionEmbedding (valueInclusion field))) =
        orthogonal (spatialDirection output) input •
          distributionPullback orthogonal
            (lineDerivOp (spatialDirection input) (distributionEmbedding (valueInclusion field))) :=
      (distributionPullback orthogonal).toLinearMap.map_smul_of_tower _ _
    _ = orthogonal (spatialDirection output) input •
        distributionEmbedding (orthogonalPullback orthogonal (weakDerivative input field)) := by
      congr 1
      change distributionPullback orthogonal
          (distributionDerivative input (distributionEmbedding (valueInclusion field))) = _
      rw [← weakDerivative_distribution, ← embedding]
    _ = distributionEmbedding
        (orthogonal (spatialDirection output) input •
          orthogonalPullback orthogonal (weakDerivative input field)) :=
      (distributionEmbedding.toLinearMap.map_smul_of_tower _ _).symm

theorem pulledDerivative_norm_sq (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldH1) :
    ∑ output : Fin 2, ‖pulledDerivative orthogonal field output‖ ^ 2 =
      ∑ input : Fin 2, ‖weakDerivative input field‖ ^ 2 := by
  let derivatives : PiLp 2 (fun _ : Fin 2 => FieldL2) :=
    WithLp.toLp 2 (fun input => orthogonalPullback orthogonal (weakDerivative input field))
  have preservation := HilbertMixing.norm_sq
    (OrthogonalCoefficients.coefficient orthogonal)
    (OrthogonalCoefficients.rowOrthogonality orthogonal) derivatives
  simp only [PiLp.norm_sq_eq_of_L2] at preservation
  change (∑ output : Fin 2, ‖pulledDerivative orthogonal field output‖ ^ 2) =
    ∑ input : Fin 2, ‖orthogonalPullback orthogonal (weakDerivative input field)‖ ^ 2 at preservation
  simpa only [orthogonalPullback_norm] using preservation

theorem normSq : NormSqGoal := by
  intro orthogonal field
  rw [orthogonalPullback_norm, pulledDerivative_norm_sq, fieldH1_norm_sq]

def pullbackField (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldH1) : FieldH1 :=
  ofWeakDerivatives (orthogonalPullback orthogonal (valueInclusion field))
    (pulledDerivative orthogonal field) (weakCoordinates orthogonal field)

theorem valueInclusion_pullbackField (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldH1) :
    valueInclusion (pullbackField orthogonal field) =
      orthogonalPullback orthogonal (valueInclusion field) := rfl

theorem weakDerivative_pullbackField (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldH1)
    (output : Fin 2) :
    weakDerivative output (pullbackField orthogonal field) = pulledDerivative orthogonal field output := rfl

theorem pullbackField_norm (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldH1) :
    ‖pullbackField orthogonal field‖ = ‖field‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  calc
    ‖pullbackField orthogonal field‖ ^ 2 =
        ‖valueInclusion (pullbackField orthogonal field)‖ ^ 2 +
          ∑ output : Fin 2, ‖weakDerivative output (pullbackField orthogonal field)‖ ^ 2 :=
      fieldH1_norm_sq _
    _ = ‖field‖ ^ 2 := by
      simp only [valueInclusion_pullbackField, weakDerivative_pullbackField]
      exact normSq orthogonal field

theorem pullbackField_add (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (first second : FieldH1) :
    pullbackField orthogonal (first + second) =
      pullbackField orthogonal first + pullbackField orthogonal second := by
  apply valueInclusion_injective
  simp only [valueInclusion_pullbackField, map_add]

theorem pullbackField_smul (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (scalar : ℂ) (field : FieldH1) :
    pullbackField orthogonal (scalar • field) = scalar • pullbackField orthogonal field := by
  apply valueInclusion_injective
  simp only [valueInclusion_pullbackField, map_smul]

theorem pullbackField_symm_apply (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldH1) :
    pullbackField orthogonal.symm (pullbackField orthogonal field) = field := by
  apply valueInclusion_injective
  rw [valueInclusion_pullbackField, valueInclusion_pullbackField, orthogonalPullback_symm_apply]

theorem pullbackField_apply_symm (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldH1) :
    pullbackField orthogonal (pullbackField orthogonal.symm field) = field := by
  apply valueInclusion_injective
  rw [valueInclusion_pullbackField, valueInclusion_pullbackField, orthogonalPullback_apply_symm]

def h1Pullback (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) : FieldH1 ≃ₗᵢ[ℂ] FieldH1 where
  toFun := pullbackField orthogonal
  invFun := pullbackField orthogonal.symm
  map_add' := pullbackField_add orthogonal
  map_smul' := pullbackField_smul orthogonal
  norm_map' := pullbackField_norm orthogonal
  left_inv := pullbackField_symm_apply orthogonal
  right_inv := pullbackField_apply_symm orthogonal

theorem valueInclusion_h1Pullback (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldH1) :
    valueInclusion (h1Pullback orthogonal field) =
      orthogonalPullback orthogonal (valueInclusion field) := rfl

theorem weakDerivative_h1Pullback (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldH1)
    (output : Fin 2) :
    weakDerivative output (h1Pullback orthogonal field) =
      ∑ input : Fin 2, orthogonal (spatialDirection output) input •
        orthogonalPullback orthogonal (weakDerivative input field) := rfl

theorem h1Pullback_norm (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldH1) :
    ‖h1Pullback orthogonal field‖ = ‖field‖ := (h1Pullback orthogonal).norm_map field

theorem h1Pullback_symm (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) :
    (h1Pullback orthogonal).symm = h1Pullback orthogonal.symm := by
  apply LinearIsometryEquiv.ext
  intro field
  rfl

theorem h1Pullback_symm_apply (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldH1) :
    h1Pullback orthogonal.symm (h1Pullback orthogonal field) = field :=
  pullbackField_symm_apply orthogonal field

theorem h1Pullback_apply_symm (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldH1) :
    h1Pullback orthogonal (h1Pullback orthogonal.symm field) = field :=
  pullbackField_apply_symm orthogonal field

theorem pullbackProof : PullbackGoal :=
  ⟨h1Pullback, valueInclusion_h1Pullback, weakDerivative_h1Pullback, h1Pullback_norm, h1Pullback_symm⟩

end Grad.WeakPullback.H1
