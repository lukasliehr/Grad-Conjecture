import AKCZ4OriginalInverseCoherence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Grad.NashMoser.InverseCalculus

/-- Dense completion of the actual core resolvent, with four independently
specified Banach grades. The inner inverse pays for the forward input, and
the outer inverse pays for the forward output. -/
theorem shiftedCompleted_resolvent
    {State Source Input HighState MiddleSource Output : Type*}
    [AddCommGroup State] [Module ℝ State] [AddCommGroup Source] [Module ℝ Source]
    [NormedAddCommGroup Input] [NormedSpace ℝ Input]
    [NormedAddCommGroup HighState] [NormedSpace ℝ HighState]
    [NormedAddCommGroup MiddleSource] [NormedSpace ℝ MiddleSource]
    [NormedAddCommGroup Output] [NormedSpace ℝ Output]
    (sourceEmbedding : Source →ₗ[ℝ] Input) (sourceDense : DenseRange sourceEmbedding)
    (highEmbedding : State →ₗ[ℝ] HighState) (middleEmbedding : Source →ₗ[ℝ] MiddleSource)
    (outputEmbedding : State →ₗ[ℝ] Output)
    (baseForward pointForward : State →ₗ[ℝ] Source) (baseInverse pointInverse : Source →ₗ[ℝ] State)
    (baseRight : ∀ source, baseForward (baseInverse source)=source)
    (pointLeft : ∀ state, pointInverse (pointForward state)=state)
    (baseLow pointLow : Input →L[ℝ] Output) (baseHigh : Input →L[ℝ] HighState)
    (pointOuter : MiddleSource →L[ℝ] Output) (baseA pointA : HighState →L[ℝ] MiddleSource)
    (baseLowCore : ∀ source, baseLow (sourceEmbedding source)=outputEmbedding (baseInverse source))
    (pointLowCore : ∀ source, pointLow (sourceEmbedding source)=outputEmbedding (pointInverse source))
    (baseHighCore : ∀ source, baseHigh (sourceEmbedding source)=highEmbedding (baseInverse source))
    (pointOuterCore : ∀ source, pointOuter (middleEmbedding source)=outputEmbedding (pointInverse source))
    (baseACore : ∀ state, baseA (highEmbedding state)=middleEmbedding (baseForward state))
    (pointACore : ∀ state, pointA (highEmbedding state)=middleEmbedding (pointForward state)) :
    pointLow-baseLow = -(pointOuter.comp (pointA-baseA)).comp baseHigh := by
  apply ContinuousLinearMap.ext
  intro source
  apply isClosed_property sourceDense
    (isClosed_eq (pointLow-baseLow).continuous (-(pointOuter.comp (pointA-baseA)).comp baseHigh).continuous) _ source
  intro core
  simp only [sub_apply, neg_apply,
    ContinuousLinearMap.comp_apply, baseLowCore, pointLowCore, baseHighCore, baseACore, pointACore]
  rw [← map_sub middleEmbedding, pointOuterCore, ← map_neg outputEmbedding, ← map_sub outputEmbedding]
  exact congrArg outputEmbedding (core_resolvent_identity baseForward pointForward baseInverse pointInverse baseRight pointLeft core)

end Grad.NashMoser.InverseCalculus
