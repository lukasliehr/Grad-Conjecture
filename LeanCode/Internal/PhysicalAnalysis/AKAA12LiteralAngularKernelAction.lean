import AKAA10ActualAngularKernelBounds
import AKAA11LiteralDerivativeKernelAction

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped BigOperators ContDiff

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Algebra
open Grad.GenericCarriers Grad.ActualAngularInverse Grad.Constraints

theorem startupAngularKernel_entry_zero (dimension : ℕ) (weight : ℝ → ℂ)
    (smooth : ContDiff ℝ ∞ weight) (output input : ℤ) (different : output ≠ input) :
    Grad.FullCellKernel.entry (startupAngularKernelData dimension weight smooth) output input = 0 := by
  apply norm_le_zero_iff.mp
  have bound := Grad.FullCellKernel.entry_norm_le (startupAngularKernelData dimension weight smooth) output input
  change ‖Grad.FullCellKernel.entry (startupAngularKernelData dimension weight smooth) output input‖ ≤
    ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
      if output = input then ‖startupAngularCoefficient dimension weight angle‖ else 0 at bound
  simpa only [different, if_false, integral_zero] using bound

theorem startupAngularKernel_coordinate (dimension : ℕ) (weight : ℝ → ℂ)
    (smooth : ContDiff ℝ ∞ weight) (field : FieldL2 dimension openUnitDisk) (output : ℤ) :
    fieldCellProjection dimension openUnitDisk output (startupAngularKernel dimension weight smooth field) =
      Grad.FullCellKernel.entry (startupAngularKernelData dimension weight smooth) output output
        (fieldCellProjection dimension openUnitDisk output field) := by
  rw [startupAngularKernel, Grad.FullCellKernel.kernel_coordinate]
  apply tsum_eq_single output
  intro input different
  rw [startupAngularKernel_entry_zero dimension weight smooth output input (Ne.symm different), zero_apply]

theorem startupAngularKernel_coordinate_ae (dimension : ℕ) (weight : ℝ → ℂ)
    (smooth : ContDiff ℝ ∞ weight) (field : FieldL2 dimension openUnitDisk) (output : ℤ) :
    ∀ᵐ point ∂volume.restrict openUnitDisk,
      fieldCellProjection dimension openUnitDisk output
        (startupAngularKernel dimension weight smooth field) point =
      (((2 * Real.pi)⁻¹ : ℝ) : ℂ) •
        ∫ angle in Icc (0 : ℝ) (2 * Real.pi), weight angle • field (planeRotationEquiv angle point) output := by
  filter_upwards [Grad.FullCellKernel.entry_field_ae (startupAngularKernelData dimension weight smooth)
    field output output] with point action
  rw [startupAngularKernel_coordinate]
  simp only [startupAngularKernelData, startupFixedKernelData, if_true] at action
  change _ = ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
    (((2 * Real.pi)⁻¹ : ℝ) : ℂ) • (weight angle • field (planeRotationEquiv angle point) output) at action
  exact action.trans (integral_smul _ _)

/-- The SAME compact primitive with precisely its single resonant angular
 projection removed, as in ANS. All integer cells are still present. -/
def startupTrueAngularInverse (dimension : ℕ) (shift : ℤ) :
    FieldL2 dimension openUnitDisk →L[ℂ] FieldL2 dimension openUnitDisk :=
  (startupPrimitiveKernel dimension shift).comp
    (ContinuousLinearMap.id ℂ _ - startupCharacterKernel dimension (-shift))

end Grad.GaugeCoefficients.Physical.RadialLedger
