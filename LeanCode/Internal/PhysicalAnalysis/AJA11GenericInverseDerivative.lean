import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

noncomputable section
set_option autoImplicit false
namespace Grad.AnnularInverseCalculus

variable {𝕜 P E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

/-- Normalize an actual two-sided inverse family to one endomorphism algebra. -/
def normalizedUnit (forward : P → E →L[𝕜] F) (inverse : P → F →L[𝕜] E)
    (right : ∀ point, (forward point).comp (inverse point) = ContinuousLinearMap.id 𝕜 F)
    (left : ∀ point, (inverse point).comp (forward point) = ContinuousLinearMap.id 𝕜 E)
    (base point : P) : (E →L[𝕜] E)ˣ where
  val := (inverse base).comp (forward point)
  inv := (inverse point).comp (forward base)
  val_inv := by
    ext field
    change inverse base (forward point (inverse point (forward base field))) = field
    have r := congrArg (fun op : F →L[𝕜] F => op (forward base field)) (right point)
    change forward point (inverse point (forward base field)) = forward base field at r
    rw [r]
    exact congrArg (fun op : E →L[𝕜] E => op field) (left base)
  inv_val := by
    ext field
    change inverse point (forward base (inverse base (forward point field))) = field
    have r := congrArg (fun op : F →L[𝕜] F => op (forward point field)) (right base)
    change forward base (inverse base (forward point field)) = forward point field at r
    rw [r]
    exact congrArg (fun op : E →L[𝕜] E => op field) (left point)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F] in
theorem normalizedInverse_value (forward : P → E →L[𝕜] F) (inverse : P → F →L[𝕜] E)
    (right : ∀ point, (forward point).comp (inverse point) = ContinuousLinearMap.id 𝕜 F)
    (left : ∀ point, (inverse point).comp (forward point) = ContinuousLinearMap.id 𝕜 E)
    (base point : P) :
    (Ring.inverse ((inverse base).comp (forward point))).comp (inverse base) = inverse point := by
  have equality := Ring.inverse_unit (normalizedUnit forward inverse right left base point)
  change Ring.inverse ((inverse base).comp (forward point)) = (inverse point).comp (forward base) at equality
  rw [equality]
  ext source
  change inverse point (forward base (inverse base source)) = inverse point source
  have r := congrArg (fun op : F →L[𝕜] F => op source) (right base)
  change forward base (inverse base source) = source at r
  rw [r]

/-- The real derivative sandwich, retaining the original scalar-linear operators. -/
def inverseSandwich (inverse : F →L[𝕜] E) : (E →L[𝕜] F) →L[ℝ] (F →L[𝕜] E) :=
  -(((ContinuousLinearMap.compL 𝕜 F E E).flip inverse).restrictScalars ℝ).comp
    (((ContinuousLinearMap.compL 𝕜 E F E) inverse).restrictScalars ℝ)

theorem inverseSandwich_apply (inverse : F →L[𝕜] E) (direction : E →L[𝕜] F) :
    inverseSandwich inverse direction = -inverse.comp (direction.comp inverse) := rfl

/-- Genuine operator-norm derivative of the SAME inverse, from both existing
inverse laws and the forward derivative. No additional neighborhood is used. -/
theorem sameInverse_hasFDerivAt [CompleteSpace E]
    (forward : P → E →L[𝕜] F) (inverse : P → F →L[𝕜] E)
    (right : ∀ point, (forward point).comp (inverse point) = ContinuousLinearMap.id 𝕜 F)
    (left : ∀ point, (inverse point).comp (forward point) = ContinuousLinearMap.id 𝕜 E)
    (point : P) (derivative : P →L[ℝ] (E →L[𝕜] F))
    (forwardDerivative : HasFDerivAt forward derivative point) :
    HasFDerivAt inverse ((inverseSandwich (inverse point)).comp derivative) point := by
  let leftCompose : (E →L[𝕜] F) →L[ℝ] (E →L[𝕜] E) :=
    ((ContinuousLinearMap.compL 𝕜 E F E) (inverse point)).restrictScalars ℝ
  let rightCompose : (E →L[𝕜] E) →L[ℝ] (F →L[𝕜] E) :=
    ((ContinuousLinearMap.compL 𝕜 F E E).flip (inverse point)).restrictScalars ℝ
  have ringDerivative := (hasFDerivAt_ringInverse (𝕜 := 𝕜)
    (normalizedUnit forward inverse right left point point)).restrictScalars ℝ
  change HasFDerivAt Ring.inverse _ (leftCompose (forward point)) at ringDerivative
  have composed := rightCompose.hasFDerivAt.comp point
    (ringDerivative.comp point (leftCompose.hasFDerivAt.comp point forwardDerivative))
  have values : (fun tau => rightCompose (Ring.inverse (leftCompose (forward tau)))) = inverse := by
    funext tau
    exact normalizedInverse_value forward inverse right left point tau
  change HasFDerivAt (fun tau => rightCompose (Ring.inverse (leftCompose (forward tau)))) _ point at composed
  rw [values] at composed
  apply composed.congr_fderiv
  apply ContinuousLinearMap.ext
  intro direction
  apply ContinuousLinearMap.ext
  intro source
  change -inverse point (forward point (inverse point (derivative direction
      (inverse point (forward point (inverse point source)))))) =
    -inverse point (derivative direction (inverse point source))
  have solve (value : F) : forward point (inverse point value) = value :=
    congrArg (fun op : F →L[𝕜] F => op value) (right point)
  rw [solve, solve]

end Grad.AnnularInverseCalculus
