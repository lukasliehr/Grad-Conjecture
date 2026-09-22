import AKBD2ProjectedParameterCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
namespace Grad.ActualDeterminantEquations
open Grad.SourceCollarFullSource

/-- The actual compact angular projection as a linear map on continuous
fields. This packages the checked integral identities inside this proof block. -/
def polarMeanFreeLinearMap : C(ℝ × ℝ,ℂ) →ₗ[ℂ] C(ℝ × ℝ,ℂ) where
  toFun field := ⟨removePolarMean field,(removePolarMean_continuous _ field.continuous)⟩
  map_add' first second := by
    apply ContinuousMap.ext
    intro angles
    exact congrFun (removePolarMean_add first second first.continuous second.continuous) angles
  map_smul' scalar field := by
    apply ContinuousMap.ext
    intro angles
    exact congrFun (removePolarMean_smul scalar field) angles

theorem polarMeanFreeLinearMap_idempotent (field : C(ℝ × ℝ,ℂ)) :
    polarMeanFreeLinearMap (polarMeanFreeLinearMap field) = polarMeanFreeLinearMap field := by
  apply ContinuousMap.ext
  intro angles
  exact congrFun (removePolarMean_idempotent field field.continuous) angles

/-- The projected radial equation and the genuine product-rule expansion
recover the original projected determinant residual. The two nested P terms
are discharged by idempotence, never by commuting P with kappa multiplication. -/
theorem projectedDeterminant_residual {Space : Type*} [AddCommGroup Space] [Module ℂ Space]
    (projection : Space →ₗ[ℂ] Space) (idempotent : ∀ value,projection (projection value)=projection value)
    (radialScale axialScale : ℂ) (raw rawRadial thirdAxial retained correction source divergence : Space)
    (expansion : rawRadial+radialScale • raw+axialScale • thirdAxial+radialScale • retained-correction=divergence)
    (radialLaw : projection rawRadial = projection
      (-radialScale • projection raw-axialScale • thirdAxial-radialScale • projection retained+source+projection correction)) :
    projection divergence = projection source := by
  rw [← expansion,map_sub,map_add,map_add,map_add,map_smul,map_smul,map_smul]
  have law : projection rawRadial = -radialScale • projection raw-axialScale • projection thirdAxial-
      radialScale • projection retained+projection source+projection correction := by
    simpa only [map_add,map_sub,map_smul,idempotent] using radialLaw
  rw [law]
  module

end Grad.ActualDeterminantEquations
