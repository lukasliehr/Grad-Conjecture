import AKAA11LiteralDerivativeKernelAction
import AKAA8FixedOrthogonalFullCellKernel

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Algebra
open Grad.GenericCarriers

def startupPointKernelData {inputDimension outputDimension : ℕ}
    (mapping : OperatorValue inputDimension outputDimension)
    (orthogonal : Grad.PDEBootstrap.Spatial ≃ₗᵢ[ℝ] Grad.PDEBootstrap.Spatial) :
    Grad.FullCellKernel.L2KernelData (Measure.dirac (0 : ℝ)) inputDimension outputDimension openUnitDisk :=
  startupFixedKernelData (Measure.dirac (0 : ℝ)) (fun _ => orthogonal)
    (fun _ => by
      intro point
      change (‖orthogonal point‖ < 1 ↔ ‖point‖ < 1)
      rw [orthogonal.norm_map])
    (orthogonal.continuous.comp continuous_snd).measurable
    (fun _ => mapping) measurable_const (integrable_const mapping)

def startupPointKernel {inputDimension outputDimension : ℕ}
    (mapping : OperatorValue inputDimension outputDimension)
    (orthogonal : Grad.PDEBootstrap.Spatial ≃ₗᵢ[ℝ] Grad.PDEBootstrap.Spatial) :=
  Grad.FullCellKernel.kernel (startupPointKernelData mapping orthogonal)

theorem startupPointKernel_norm {inputDimension outputDimension : ℕ}
    (mapping : OperatorValue inputDimension outputDimension)
    (orthogonal : Grad.PDEBootstrap.Spatial ≃ₗᵢ[ℝ] Grad.PDEBootstrap.Spatial) :
    ‖startupPointKernel mapping orthogonal‖ ≤ ‖mapping‖ := by
  have bound := Grad.FullCellKernel.kernel_norm_le (startupPointKernelData mapping orthogonal)
  change ‖startupPointKernel mapping orthogonal‖ ≤ Real.sqrt
    ((∫ _parameter : ℝ, ‖mapping‖ ∂Measure.dirac (0 : ℝ)) *
     (∫ _parameter : ℝ, ‖mapping‖ ∂Measure.dirac (0 : ℝ))) at bound
  simpa only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul,
    Real.sqrt_mul_self (norm_nonneg mapping)] using bound

theorem startupPointKernel_entry_zero {inputDimension outputDimension : ℕ}
    (mapping : OperatorValue inputDimension outputDimension)
    (orthogonal : Grad.PDEBootstrap.Spatial ≃ₗᵢ[ℝ] Grad.PDEBootstrap.Spatial)
    (output input : ℤ) (different : output ≠ input) :
    Grad.FullCellKernel.entry (startupPointKernelData mapping orthogonal) output input = 0 := by
  apply norm_le_zero_iff.mp
  have bound := Grad.FullCellKernel.entry_norm_le (startupPointKernelData mapping orthogonal) output input
  change ‖Grad.FullCellKernel.entry (startupPointKernelData mapping orthogonal) output input‖ ≤
    ∫ _parameter : ℝ, (if output = input then ‖mapping‖ else 0) ∂Measure.dirac (0 : ℝ) at bound
  simpa only [different, if_false, integral_zero] using bound

theorem startupPointKernel_coordinate {inputDimension outputDimension : ℕ}
    (mapping : OperatorValue inputDimension outputDimension)
    (orthogonal : Grad.PDEBootstrap.Spatial ≃ₗᵢ[ℝ] Grad.PDEBootstrap.Spatial)
    (field : FieldL2 inputDimension openUnitDisk) (output : ℤ) :
    fieldCellProjection outputDimension openUnitDisk output (startupPointKernel mapping orthogonal field) =
      Grad.FullCellKernel.entry (startupPointKernelData mapping orthogonal) output output
        (fieldCellProjection inputDimension openUnitDisk output field) := by
  rw [startupPointKernel, Grad.FullCellKernel.kernel_coordinate]
  apply tsum_eq_single output
  intro input different
  rw [startupPointKernel_entry_zero mapping orthogonal output input (Ne.symm different), zero_apply]

theorem startupPointKernel_coordinate_ae {inputDimension outputDimension : ℕ}
    (mapping : OperatorValue inputDimension outputDimension)
    (orthogonal : Grad.PDEBootstrap.Spatial ≃ₗᵢ[ℝ] Grad.PDEBootstrap.Spatial)
    (field : FieldL2 inputDimension openUnitDisk) (output : ℤ) :
    ∀ᵐ point ∂volume.restrict openUnitDisk,
      fieldCellProjection outputDimension openUnitDisk output
        (startupPointKernel mapping orthogonal field) point = mapping (field (orthogonal point) output) := by
  filter_upwards [Grad.FullCellKernel.entry_field_ae (startupPointKernelData mapping orthogonal)
    field output output] with point action
  rw [startupPointKernel_coordinate]
  conv at action =>
    rhs
    simp only [startupPointKernelData, startupFixedKernelData, if_true]
  change _ = ∫ _parameter : ℝ, mapping (field (orthogonal point) output) ∂Measure.dirac (0 : ℝ) at action
  simpa only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] using action

end Grad.GaugeCoefficients.Physical.RadialLedger
