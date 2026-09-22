import AKAY31RawRadialProjectionTests

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set MeasureTheory

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.KernelPullback.Domain

theorem startupField_ae_ext {dimension : ℕ} (first second : StartupL2 dimension)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, first point cell = second point cell) :
    first = second := by
  apply Lp.ext
  filter_upwards [same] with point equal
  exact lp.ext (funext equal)

theorem startupPointKernel_field_ae {input output : ℕ} (mapping : OperatorValue input output)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (field : StartupL2 input) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (startupPointKernel mapping orthogonal field) point cell = mapping (field (orthogonal point) cell) := by
  have rows : ∀ cell : ℤ, ∀ᵐ point ∂volume.restrict openUnitDisk,
      (startupPointKernel mapping orthogonal field) point cell = mapping (field (orthogonal point) cell) := by
    intro cell
    filter_upwards [startupPointKernel_coordinate_ae mapping orthogonal field cell,
      fieldCellProjection_ae output openUnitDisk (startupPointKernel mapping orthogonal field)] with point actual projection
    rw [projection cell] at actual
    exact actual
  exact ae_all_iff.mpr rows

theorem startupOrthogonal_disk_preserving (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) :
    MeasurePreserving orthogonal (volume.restrict openUnitDisk) (volume.restrict openUnitDisk) :=
  domainMeasurePreserving openUnitDisk openUnitDisk_isOpen.measurableSet orthogonal
    (fun point => by change ‖orthogonal point‖ < 1 ↔ ‖point‖ < 1; rw [orthogonal.norm_map])

theorem startupPointKernel_comp {input middle output : ℕ}
    (first : OperatorValue middle output) (second : OperatorValue input middle)
    (outer inner : Spatial ≃ₗᵢ[ℝ] Spatial) :
    (startupPointKernel first outer).comp (startupPointKernel second inner) =
      startupPointKernel (first.comp second) (outer.trans inner) := by
  apply ContinuousLinearMap.ext
  intro field
  apply startupField_ae_ext
  filter_upwards [startupPointKernel_field_ae first outer (startupPointKernel second inner field),
    (startupOrthogonal_disk_preserving outer).quasiMeasurePreserving.ae (startupPointKernel_field_ae second inner field),
    startupPointKernel_field_ae (first.comp second) (outer.trans inner) field] with point firstSame secondSame composedSame
  intro cell
  change (startupPointKernel first outer (startupPointKernel second inner field)) point cell = _
  rw [firstSame cell, secondSame cell, composedSame cell]
  rfl

theorem originalValueKernel_comp {input middle output : ℕ}
    (first : OperatorValue middle output) (second : OperatorValue input middle) :
    (originalValueKernel first).comp (originalValueKernel second) = originalValueKernel (first.comp second) :=
  startupPointKernel_comp first second (LinearIsometryEquiv.refl ℝ _) (LinearIsometryEquiv.refl ℝ _)

theorem originalValueKernel_id (dimension : ℕ) :
    originalValueKernel (ContinuousLinearMap.id ℂ (PhysicalValue dimension)) = ContinuousLinearMap.id ℂ (StartupL2 dimension) := by
  apply ContinuousLinearMap.ext
  intro field
  apply startupField_ae_ext
  exact startupPointKernel_field_ae _ (LinearIsometryEquiv.refl ℝ _) field

theorem originalValueKernel_neg {input output : ℕ} (mapping : OperatorValue input output) :
    originalValueKernel (-mapping) = -originalValueKernel mapping := by
  apply ContinuousLinearMap.ext
  intro field
  apply startupField_ae_ext
  filter_upwards [startupPointKernel_field_ae (-mapping) (LinearIsometryEquiv.refl ℝ _) field,
    startupPointKernel_field_ae mapping (LinearIsometryEquiv.refl ℝ _) field,
    Lp.coeFn_neg (originalValueKernel mapping field)] with point first second negative
  change ∀ cell : ℤ, (originalValueKernel (-mapping) field) point cell = -mapping (field point cell) at first
  change ∀ cell : ℤ, (originalValueKernel mapping field) point cell = mapping (field point cell) at second
  intro cell
  change (originalValueKernel (-mapping) field) point cell = (-originalValueKernel mapping field) point cell
  rw [first cell]
  rw [negative]
  simp only [lp.coeFn_neg, Pi.neg_apply, second cell]

theorem startupQuarter_square :
    (originalValueKernel quarterValueMap).comp (originalValueKernel quarterValueMap) =
      -ContinuousLinearMap.id ℂ (StartupL2 2) := by
  rw [originalValueKernel_comp]
  have square : quarterValueMap.comp quarterValueMap = -ContinuousLinearMap.id ℂ (PhysicalValue 2) := by
    apply ContinuousLinearMap.ext
    intro value
    exact quarterValueMap_square value
  rw [square, originalValueKernel_neg, originalValueKernel_id]

end Grad.CartesianStartup
