import AJA11GenericInverseDerivative
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
set_option autoImplicit false
open scoped ContDiff
namespace Grad.AnnularInverseCalculus

variable {𝕜 P E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

/-- Smoothness of the SAME inverse family on its original domain. -/
theorem sameInverse_contDiff [CompleteSpace E]
    (forward : P → E →L[𝕜] F) (inverse : P → F →L[𝕜] E)
    (right : ∀ point, (forward point).comp (inverse point) = ContinuousLinearMap.id 𝕜 F)
    (left : ∀ point, (inverse point).comp (forward point) = ContinuousLinearMap.id 𝕜 E)
    (smooth : ContDiff ℝ ∞ forward) : ContDiff ℝ ∞ inverse := by
  rw [contDiff_iff_contDiffAt]
  intro point
  let leftCompose : (E →L[𝕜] F) →L[ℝ] (E →L[𝕜] E) :=
    ((ContinuousLinearMap.compL 𝕜 E F E) (inverse point)).restrictScalars ℝ
  let rightCompose : (E →L[𝕜] E) →L[ℝ] (F →L[𝕜] E) :=
    ((ContinuousLinearMap.compL 𝕜 F E E).flip (inverse point)).restrictScalars ℝ
  have ringSmooth := (contDiffAt_ringInverse 𝕜 (n := ∞)
    (normalizedUnit forward inverse right left point point)).restrict_scalars ℝ
  change ContDiffAt ℝ ∞ Ring.inverse (leftCompose (forward point)) at ringSmooth
  have composed := rightCompose.contDiff.contDiffAt.comp point
    (ringSmooth.comp point ((leftCompose.contDiff.comp smooth).contDiffAt))
  have values : (fun tau => rightCompose (Ring.inverse (leftCompose (forward tau)))) = inverse := by
    funext tau
    exact normalizedInverse_value forward inverse right left point tau
  change ContDiffAt ℝ ∞ (fun tau => rightCompose (Ring.inverse (leftCompose (forward tau)))) point at composed
  rw [values] at composed
  exact composed

end Grad.AnnularInverseCalculus
