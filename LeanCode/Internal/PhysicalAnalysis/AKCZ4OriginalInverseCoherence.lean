import AKCZ3OriginalShiftedInverseLaws

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
namespace Grad.NashMoser.InverseCalculus
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades

variable (parameters : PhaseParameters) (reference : Seed.Parameters) (inside : reference ∈ Seed.parameterDomain)
    (inverse : sourceSmoothRange parameters →ₗ[ℝ] stateSmoothRange parameters reference inside)

/-- Completions of the SAME core inverse commute with both original grade
inclusions. Every constant can be the bound supplied at that exact grade. -/
theorem completedOriginalInverse_coherent
    (lowSource highSource lowOutput highOutput : ℕ)
    (sourceLarge : 3 ≤ lowSource) (outputLarge : 3 ≤ lowOutput)
    (sourceOrdered : lowSource ≤ highSource) (outputOrdered : lowOutput ≤ highOutput)
    (lowConstant highConstant : ℝ)
    (lowBound : ∀ source, ‖stateSmoothEmbedding parameters reference inside lowOutput outputLarge (inverse source)‖ ≤
      lowConstant*‖sourceSmoothEmbedding parameters lowSource sourceLarge source‖)
    (highBound : ∀ source, ‖stateSmoothEmbedding parameters reference inside highOutput (outputLarge.trans outputOrdered) (inverse source)‖ ≤
      highConstant*‖sourceSmoothEmbedding parameters highSource (sourceLarge.trans sourceOrdered) source‖) :
    (completedOriginalInverse parameters reference inside lowSource lowOutput sourceLarge outputLarge inverse lowConstant lowBound).comp
      (sourceLowering parameters sourceLarge sourceOrdered) =
    (stateLowering parameters reference inside outputLarge outputOrdered).comp
      (completedOriginalInverse parameters reference inside highSource highOutput (sourceLarge.trans sourceOrdered)
        (outputLarge.trans outputOrdered) inverse highConstant highBound) := by
  apply ContinuousLinearMap.ext
  intro source
  apply isClosed_property (sourceSmoothEmbedding_denseRange parameters highSource (sourceLarge.trans sourceOrdered))
    (isClosed_eq
      ((completedOriginalInverse parameters reference inside lowSource lowOutput sourceLarge outputLarge inverse lowConstant lowBound).continuous.comp
        (sourceLowering parameters sourceLarge sourceOrdered).continuous)
      ((stateLowering parameters reference inside outputLarge outputOrdered).continuous.comp
        (completedOriginalInverse parameters reference inside highSource highOutput (sourceLarge.trans sourceOrdered)
          (outputLarge.trans outputOrdered) inverse highConstant highBound).continuous)) _ source
  intro core
  simp only [Function.comp_apply]
  simp only [sourceLowering_core, completedOriginalInverse_core, stateLowering_core]

end Grad.NashMoser.InverseCalculus
