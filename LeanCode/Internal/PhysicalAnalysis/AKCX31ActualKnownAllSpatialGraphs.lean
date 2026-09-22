import AKCX30SameOriginalSourceAllOrder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers
open Grad.ActualScalarWeakEquations Grad.SpatialDilation Grad.WeightedJets
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.Constraints Grad.Constraints.Gauges
namespace StartupSignedFirstFamily

variable (parameters : PhaseParameters) (data : SmoothQuotient parameters)
  (length : ℝ) (positive : 0 < length) (order : ℕ)

theorem knownForce_allSpatialGrade :
    (knownForce parameters data length positive).toStartupSignedFamily.HasSpatialGrade order := by
  exact (StartupSpatialAction.radial 0).preserves order _
    (source_allSpatialGrade parameters (cartesianSourceVector data) length positive.ne'
      (originalStartupScale length positive) order)

theorem knownThird_allSpatialGrade :
    (knownThird parameters data length positive).toStartupSignedFamily.HasSpatialGrade order := by
  exact (source_allSpatialGrade parameters (data 3) length positive.ne'
    (originalStartupScale length positive) order).smul (length⁻¹ : ℂ)

theorem determinant_allSpatialGrade :
    (determinant parameters data length positive).toStartupSignedFamily.HasSpatialGrade order := by
  exact (source_allSpatialGrade parameters (data 2) length positive.ne'
    (originalStartupScale length positive) order).smul (((min 1 length / 4)/length : ℝ) : ℂ)

private theorem principalFixed_allSpatialGrade {L ell : ℝ} (order : ℕ)
    (family : StartupSignedFamily 3 L ell) (regular : family.HasSpatialGrade order)
    (outer inner : Fin 2) (row : Fin 3) :
    ((StartupSignedAction.principalFixed outer inner row).action family).HasSpatialGrade order := by
  apply ((StartupSpatialAction.principalFixed 0 outer inner row).preserves order family regular).congr
  rw [StartupSignedAction.sameField,StartupSignedAction.sameField,StartupSpatialAction.principalFixed_coarse]
  rfl

theorem knownTensor_allSpatialGrade {L ell : ℝ} (order : ℕ)
    (force : StartupSignedFirstFamily 2 L ell) (third : StartupSignedFirstFamily 1 L ell)
    (forceRegular : force.toStartupSignedFamily.HasSpatialGrade order)
    (thirdRegular : third.toStartupSignedFamily.HasSpatialGrade order) (outer inner : Fin 2) :
    (knownTensor force third outer inner).toStartupSignedFamily.HasSpatialGrade order := by
  have first := principalFixed_allSpatialGrade order _
    ((StartupSpatialAction.value 0 planarInclusionMap).preserves order _ (forceRegular.smul (-1))) outer inner 0
  have second := principalFixed_allSpatialGrade order _
    ((StartupSpatialAction.value 0 toroidalInclusionMap).preserves order _ thirdRegular) outer inner 1
  have flux := (StartupSpatialAction.value 0 quarterValueMap).preserves order _
    ((StartupSpatialAction.average 0).preserves order _ forceRegular)
  have third := principalFixed_allSpatialGrade order _
    ((StartupSpatialAction.value 0 planarInclusionMap).preserves order _ (flux.smul (1/2))) outer inner 2
  exact (first.add second).add third

end StartupSignedFirstFamily
end Grad.CartesianStartup
