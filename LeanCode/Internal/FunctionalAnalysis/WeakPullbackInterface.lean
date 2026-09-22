import OrthogonalPullback

noncomputable section

open MeasureTheory LineDeriv Grad.PDEBootstrap Grad.KernelPullback
open scoped SchwartzMap

namespace Grad.WeakPullback

def testPullback (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) :
    𝓢(Spatial, ℂ) →L[ℂ] 𝓢(Spatial, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ orthogonal.toContinuousLinearEquiv

def distributionPullback (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) :
    FieldDistribution →L[ℂ] FieldDistribution :=
  PointwiseConvergenceCLM.precomp CellValues (testPullback orthogonal.symm)

def EmbeddingGoal : Prop :=
  ∀ (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldL2),
    distributionEmbedding (orthogonalPullback orthogonal field) =
      distributionPullback orthogonal (distributionEmbedding field)

def DirectionalGoal : Prop :=
  ∀ (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (direction : Spatial)
    (distribution : FieldDistribution),
    lineDerivOp direction (distributionPullback orthogonal distribution) =
      distributionPullback orthogonal (lineDerivOp (orthogonal direction) distribution)

def LiteralConsumerGoal : Prop :=
  ∀ (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : FieldL2)
    (test : 𝓢(Spatial, ℂ)),
    ∫ point : Spatial, test point • (orthogonalPullback orthogonal field) point =
      ∫ point : Spatial, test (orthogonal.symm point) • field point

#check (show FieldL2 →L[ℂ] FieldDistribution from distributionEmbedding)
#check SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv
#check Lp.toTemperedDistribution_apply
#check MeasurePreserving.integral_comp
#check LinearIsometryEquiv.toHomeomorph
#check Homeomorph.measurableEmbedding
#check UniformConvergenceCLM.ext
#check TemperedDistribution.lineDerivOp_apply_apply

end Grad.WeakPullback
