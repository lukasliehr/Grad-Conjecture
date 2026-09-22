import AKBW8FixedCovectorCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000

open MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra (OperatorValue)
open Grad.GaugeCoefficients.Physical.RadialLedger

variable {Parameter : Type*} [MeasurableSpace Parameter]
    (measure : Measure Parameter) [SigmaFinite measure]
    {input output : ℕ}
    (orthogonal : Parameter → Spatial ≃ₗᵢ[ℝ] Spatial)
    (invariant : ∀ parameter, Grad.KernelPullback.Domain.Invariant openUnitDisk (orthogonal parameter))
    (actionMeasurable : Measurable (fun pair : Parameter × Spatial => orthogonal pair.1 pair.2))
    (coefficient : Parameter → OperatorValue input output)
    (measurable : Measurable coefficient) (integrable : Integrable coefficient measure)

theorem startupFixed_entry_zero (outer inner : ℤ) (different : outer ≠ inner) :
    Grad.FullCellKernel.entry (startupFixedKernelData measure orthogonal invariant actionMeasurable
      coefficient measurable integrable) outer inner = 0 := by
  apply norm_le_zero_iff.mp
  have bound := Grad.FullCellKernel.entry_norm_le
    (startupFixedKernelData measure orthogonal invariant actionMeasurable coefficient measurable integrable) outer inner
  change ‖_‖ ≤ ∫ parameter, (if outer = inner then ‖coefficient parameter‖ else 0) ∂measure at bound
  simpa only [if_neg different, integral_zero] using bound

theorem startupFixed_coordinate (field : StartupL2 input) (cell : ℤ) :
    fieldCellProjection output openUnitDisk cell
      (Grad.FullCellKernel.kernel (startupFixedKernelData measure orthogonal invariant actionMeasurable
        coefficient measurable integrable) field) =
      Grad.FullCellKernel.entry (startupFixedKernelData measure orthogonal invariant actionMeasurable
        coefficient measurable integrable) cell cell (fieldCellProjection input openUnitDisk cell field) := by
  rw [Grad.FullCellKernel.kernel_coordinate]
  apply tsum_eq_single cell
  intro other different
  rw [startupFixed_entry_zero measure orthogonal invariant actionMeasurable coefficient measurable integrable cell other (Ne.symm different), zero_apply]

theorem startupFixed_coordinate_ae (field : StartupL2 input) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      Grad.FullCellKernel.kernel (startupFixedKernelData measure orthogonal invariant actionMeasurable
        coefficient measurable integrable) field point cell =
      ∫ parameter, coefficient parameter (field (orthogonal parameter point) cell) ∂measure := by
  apply ae_all_iff.mpr
  intro cell
  filter_upwards [Grad.FullCellKernel.entry_field_ae
    (startupFixedKernelData measure orthogonal invariant actionMeasurable coefficient measurable integrable) field cell cell,
    fieldCellProjection_ae output openUnitDisk
      (Grad.FullCellKernel.kernel (startupFixedKernelData measure orthogonal invariant actionMeasurable coefficient measurable integrable) field)]
      with point action coordinates
  rw [← coordinates cell, startupFixed_coordinate measure orthogonal invariant actionMeasurable coefficient measurable integrable]
  simpa only [startupFixedKernelData, if_true] using action

end Grad.CartesianStartup
