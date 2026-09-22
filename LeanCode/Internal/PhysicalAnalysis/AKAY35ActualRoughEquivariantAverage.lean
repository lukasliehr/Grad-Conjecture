import AKAY34GenuineRadialReflectionIdentity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.RepresentedKernel Grad.RepresentedKernel.WeakDerivatives

def startupAverageCoefficient (angle : ℝ) : OperatorValue 2 2 :=
  (((2 * Real.pi)⁻¹ : ℝ) : ℂ) • rotationValueMap (-angle)

theorem startupAverageCoefficient_continuous : Continuous startupAverageCoefficient := by
  unfold startupAverageCoefficient rotationValueMap
  fun_prop

def startupAverageRawData :
    RawKernelData (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) 2 2 openUnitDisk :=
  startupFixedRawData (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) planeRotationEquiv
    (fun angle => by
      intro point
      change (‖planeRotationEquiv angle point‖ < 1 ↔ ‖point‖ < 1)
      rw [(planeRotationEquiv angle).norm_map])
    continuous_planeRotation_joint.measurable startupAverageCoefficient
    startupAverageCoefficient_continuous.measurable startupAverageCoefficient_continuous.integrableOn_Icc

theorem startupAverageCoefficient_helicity (angle : ℝ) (value : PhysicalValue 2) :
    positiveHelicity (startupAngularCoefficient 2 (angularCharacter 1) angle value) +
      negativeHelicity (startupAngularCoefficient 2 (angularCharacter (-1)) angle value) =
      startupAverageCoefficient angle value := by
  simp only [startupAngularCoefficient, startupAverageCoefficient, smul_apply, ContinuousLinearMap.id_apply,
    map_smul, rotationValueMap_character, smul_add]

/-- Literal value rotation O(-angle) and spatial rotation O(angle) for the
actual full-cell equivariant average on arbitrary rough fields. -/
theorem startupAverageKernel_action_ae (field : StartupL2 2) (cell : ℤ) :
    ∀ᵐ point ∂volume.restrict openUnitDisk,
      (originalAverageKernel field) point cell =
        ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
          startupAverageCoefficient angle (field (planeRotationEquiv angle point) cell) := by
  filter_upwards [startupPointKernel_field_ae positiveHelicity (LinearIsometryEquiv.refl ℝ _) (startupCharacterKernel 2 1 field),
    startupPointKernel_field_ae negativeHelicity (LinearIsometryEquiv.refl ℝ _) (startupCharacterKernel 2 (-1) field),
    startupAngularKernel_action_ae 2 (angularCharacter 1) (angularCharacter_smooth 1) field cell,
    startupAngularKernel_action_ae 2 (angularCharacter (-1)) (angularCharacter_smooth (-1)) field cell,
    startupAngularKernel_row_integrable 2 (angularCharacter 1) (angularCharacter_smooth 1) field cell,
    startupAngularKernel_row_integrable 2 (angularCharacter (-1)) (angularCharacter_smooth (-1)) field cell,
    Lp.coeFn_add (originalValueKernel positiveHelicity (startupCharacterKernel 2 1 field))
      (originalValueKernel negativeHelicity (startupCharacterKernel 2 (-1) field))]
    with point positive negative positiveAction negativeAction positiveIntegrable negativeIntegrable addSame
  change ∀ cell : ℤ, (originalValueKernel positiveHelicity (startupCharacterKernel 2 1 field)) point cell =
    positiveHelicity ((startupCharacterKernel 2 1 field) point cell) at positive
  change ∀ cell : ℤ, (originalValueKernel negativeHelicity (startupCharacterKernel 2 (-1) field)) point cell =
    negativeHelicity ((startupCharacterKernel 2 (-1) field) point cell) at negative
  change (startupCharacterKernel 2 1 field) point cell = _ at positiveAction
  change (startupCharacterKernel 2 (-1) field) point cell = _ at negativeAction
  change ((originalValueKernel positiveHelicity (startupCharacterKernel 2 1 field)) +
    (originalValueKernel negativeHelicity (startupCharacterKernel 2 (-1) field))) point cell = _
  rw [addSame]
  simp only [Pi.add_apply, lp.coeFn_add]
  rw [positive cell, negative cell, positiveAction, negativeAction,
    ← positiveHelicity.integral_comp_comm positiveIntegrable,
    ← negativeHelicity.integral_comp_comm negativeIntegrable,
    ← integral_add (positiveHelicity.integrable_comp positiveIntegrable) (negativeHelicity.integrable_comp negativeIntegrable)]
  apply integral_congr_ae
  filter_upwards [] with angle
  exact startupAverageCoefficient_helicity angle _

end Grad.CartesianStartup
