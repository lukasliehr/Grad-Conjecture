import AKBL11SameOriginalMatrixField
import AKBE16RadialProjectionLocality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set MeasureTheory
open scoped Interval
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.Constraints Grad.PhysicalFamily Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Algebra

/-- Character projection has its exact closed-value representative for a
merely measurable rough input. Global continuity at the axis is unnecessary;
the integral is transported through the actual measure-preserving rotations. -/
theorem startupCharacter_closedRepresentative {dimension : ℕ} (mode : ℤ)
    (field : StartupL2 dimension) (cell : ℤ) (raw : ClosedDisk → PhysicalValue dimension)
    (same : (fun point => field point cell) =ᵐ[volume.restrict openUnitDisk] closedFieldExtension raw) :
    (fun point => startupCharacterKernel dimension mode field point cell) =ᵐ[volume.restrict openUnitDisk]
      closedFieldExtension (closedCharacterProjection mode raw) := by
  have transported := Grad.KernelIntegral.transported_ae_eq_sections
    (volume.restrict (Icc (0 : ℝ) (2*Real.pi))) openUnitDisk_isOpen.measurableSet planeRotationEquiv
    (fun angle point => by change ‖planeRotationEquiv angle point‖ < 1 ↔ ‖point‖ < 1; rw [LinearIsometryEquiv.norm_map])
    continuous_planeRotation_joint.measurable same
  filter_upwards [startupAngularKernel_action_ae dimension (angularCharacter mode) (angularCharacter_smooth mode) field cell,
    transported,ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point action moved inside
  let closed : ClosedDisk := ⟨point,openDiskMembershipClosed point inside⟩
  have extension := closedFieldExtension_value (closedCharacterProjection mode raw) closed
  change closedFieldExtension (closedCharacterProjection mode raw) point = _ at extension
  change startupCharacterKernel dimension mode field point cell = _ at action
  rw [action,extension]
  change _ = angularProjectionValue mode (closedFieldExtension raw) point
  unfold angularProjectionValue
  rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2*Real.pi),← integral_Icc_eq_integral_Ioc,← integral_smul]
  apply integral_congr_ae
  filter_upwards [moved] with angle equal
  rw [equal]
  simp only [startupAngularCoefficient,smul_apply,ContinuousLinearMap.id_apply]
  congr 2
  exact congrArg (closedFieldExtension raw) (physicalRotation_eq_orthogonal angle point).symm

/-- Constant value maps preserve the literal rough closed representative. -/
theorem startupValue_closedRepresentative {input output : ℕ} (mapping : OperatorValue input output)
    (field : StartupL2 input) (cell : ℤ) (raw : ClosedDisk → PhysicalValue input)
    (same : (fun point => field point cell) =ᵐ[volume.restrict openUnitDisk] closedFieldExtension raw) :
    (fun point => originalValueKernel mapping field point cell) =ᵐ[volume.restrict openUnitDisk]
      closedFieldExtension (fun closed => mapping (raw closed)) := by
  filter_upwards [startupPointKernel_field_ae mapping (LinearIsometryEquiv.refl ℝ _) field,
    same,ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point value original inside
  let closed : ClosedDisk := ⟨point,openDiskMembershipClosed point inside⟩
  have inputAt := closedFieldExtension_value raw closed
  have outputAt := closedFieldExtension_value (fun closed => mapping (raw closed)) closed
  change closedFieldExtension raw point = _ at inputAt
  change closedFieldExtension (fun closed => mapping (raw closed)) point = _ at outputAt
  change ∀ index : ℤ, originalValueKernel mapping field point index = mapping (field point index) at value
  exact (value cell).trans ((congrArg mapping (original.trans inputAt)).trans outputAt.symm)

end Grad.CartesianStartup
