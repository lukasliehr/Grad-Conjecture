import AKAY32RoughFixedMapAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.RepresentedKernel Grad.RepresentedKernel.WeakDerivatives

def startupAngularRawDataDim (dimension : ℕ) (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight) :
    RawKernelData (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) dimension dimension openUnitDisk :=
  startupFixedRawData (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) planeRotationEquiv
    (fun angle => by
      intro point
      change (‖planeRotationEquiv angle point‖ < 1 ↔ ‖point‖ < 1)
      rw [(planeRotationEquiv angle).norm_map])
    continuous_planeRotation_joint.measurable (startupAngularCoefficient dimension weight)
    (startupAngularCoefficient_continuous dimension weight smooth).measurable
    (startupAngularCoefficient_continuous dimension weight smooth).integrableOn_Icc

theorem startupAngularKernel_action_ae (dimension : ℕ) (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight)
    (field : StartupL2 dimension) (cell : ℤ) :
    ∀ᵐ point ∂volume.restrict openUnitDisk,
      (startupAngularKernel dimension weight smooth field) point cell =
        ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
          startupAngularCoefficient dimension weight angle (field (planeRotationEquiv angle point) cell) := by
  filter_upwards [Grad.FullCellKernel.entry_field_ae (startupAngularKernelData dimension weight smooth) field cell cell,
    fieldCellProjection_ae dimension openUnitDisk (startupAngularKernel dimension weight smooth field)] with point action projection
  rw [← projection cell, startupAngularKernel_coordinate]
  simpa only [startupAngularKernelData, startupFixedKernelData, if_true] using action

theorem startupAngularKernel_row_integrable (dimension : ℕ) (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight)
    (field : StartupL2 dimension) (cell : ℤ) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, Integrable
      (fun angle => startupAngularCoefficient dimension weight angle (field (planeRotationEquiv angle point) cell))
      (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) := by
  simpa only [startupAngularRawDataDim, startupFixedRawData, startupFixedKernelData, if_true] using
    coefficientCell_row_integrable (startupAngularRawDataDim dimension weight smooth) cell cell field

/-- Fixed value maps commute with the actual angular kernel on the SAME rough field. -/
theorem startupAngularKernel_value_commute {input output : ℕ} (mapping : OperatorValue input output)
    (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight) :
    (startupAngularKernel output weight smooth).comp (originalValueKernel mapping) =
      (originalValueKernel mapping).comp (startupAngularKernel input weight smooth) := by
  apply ContinuousLinearMap.ext
  intro field
  apply startupField_ae_ext
  apply ae_all_iff.mpr
  intro cell
  have same : (fun point => (originalValueKernel mapping field) point cell) =ᵐ[volume.restrict openUnitDisk]
      fun point => mapping (field point cell) := by
    filter_upwards [startupPointKernel_field_ae mapping (LinearIsometryEquiv.refl ℝ _) field] with point identity
    exact identity cell
  have transported := Grad.KernelIntegral.transported_ae_eq_sections
    (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) openUnitDisk_isOpen.measurableSet planeRotationEquiv
    (fun angle point => by change ‖planeRotationEquiv angle point‖ < 1 ↔ ‖point‖ < 1; rw [LinearIsometryEquiv.norm_map])
    continuous_planeRotation_joint.measurable same
  filter_upwards [startupAngularKernel_action_ae output weight smooth (originalValueKernel mapping field) cell,
    startupPointKernel_field_ae mapping (LinearIsometryEquiv.refl ℝ _) (startupAngularKernel input weight smooth field),
    startupAngularKernel_action_ae input weight smooth field cell,
    startupAngularKernel_row_integrable input weight smooth field cell, transported]
    with point left mapped right integrable transported
  change (startupAngularKernel output weight smooth (originalValueKernel mapping field)) point cell =
    (originalValueKernel mapping (startupAngularKernel input weight smooth field)) point cell
  change ∀ cell : ℤ, (originalValueKernel mapping (startupAngularKernel input weight smooth field)) point cell =
    mapping ((startupAngularKernel input weight smooth field) point cell) at mapped
  rw [left, mapped cell, right, ← mapping.integral_comp_comm integrable]
  apply integral_congr_ae
  filter_upwards [transported] with angle actual
  rw [actual]
  simp only [startupAngularCoefficient, smul_apply, ContinuousLinearMap.id_apply, map_smul]

end Grad.CartesianStartup
