import WeakPullbackInterface

noncomputable section

open MeasureTheory LineDeriv Grad.PDEBootstrap Grad.KernelPullback
open scoped SchwartzMap

namespace Grad.WeakPullback

theorem testPullback_apply (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (test : 𝓢(Spatial, ℂ)) (point : Spatial) :
    testPullback orthogonal test point = test (orthogonal point) := rfl

theorem distributionPullback_apply (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (distribution : FieldDistribution) (test : 𝓢(Spatial, ℂ)) :
    distributionPullback orthogonal distribution test =
      distribution (testPullback orthogonal.symm test) := rfl

theorem embedding_apply (field : FieldL2) (test : 𝓢(Spatial, ℂ)) :
    distributionEmbedding field test = ∫ point : Spatial, test point • field point :=
  Lp.toTemperedDistribution_apply field test

theorem literalConsumer : LiteralConsumerGoal := by
  intro orthogonal field test
  calc
    (∫ point : Spatial, test point • (orthogonalPullback orthogonal field) point) =
        ∫ point : Spatial, test point • field (orthogonal point) := by
      apply integral_congr_ae
      filter_upwards [orthogonalPullback_ae orthogonal field] with point equality
      rw [equality]
    _ = ∫ point : Spatial, test (orthogonal.symm point) • field point := by
      simpa only [LinearIsometryEquiv.symm_apply_apply] using
        orthogonal.measurePreserving.integral_comp orthogonal.toHomeomorph.measurableEmbedding
          (fun point : Spatial => test (orthogonal.symm point) • field point)

theorem embedding : EmbeddingGoal := by
  intro orthogonal field
  apply UniformConvergenceCLM.ext
  intro test
  rw [distributionPullback_apply, embedding_apply, embedding_apply]
  exact literalConsumer orthogonal field test

theorem directional : DirectionalGoal := by
  intro orthogonal direction distribution
  apply UniformConvergenceCLM.ext
  intro test
  change distribution (testPullback orthogonal.symm (-lineDerivOp direction test)) =
    distribution (-lineDerivOp (orthogonal direction) (testPullback orthogonal.symm test))
  congr 1
  rw [map_neg]
  congr 1
  symm
  simpa only [testPullback, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.symm_apply_apply] using
    SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv ℂ (orthogonal direction)
      orthogonal.symm.toContinuousLinearEquiv test

end Grad.WeakPullback
