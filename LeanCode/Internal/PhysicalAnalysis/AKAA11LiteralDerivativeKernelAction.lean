import AKAA7FullCartesianDerivativeKernel

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.Allocation Grad.GenericCarriers

theorem startup_entry_ae {Parameter : Type*} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension : ℕ} {domain : Set Grad.PDEBootstrap.Spatial}
    (data : Grad.FullCellKernel.L2KernelData measure inputDimension outputDimension domain)
    (output input : ℤ) (field : Lp (PhysicalValue inputDimension) 2 (volume.restrict domain)) :
    ∀ᵐ point ∂volume.restrict domain,
      Grad.FullCellKernel.entry data output input field point =
        ∫ parameter, data.coefficient output input (parameter, point)
          (field (data.orthogonal parameter point)) ∂measure :=
  Grad.KernelIntegral.integralKernelCLM_apply_ae measure data.domainMeasurable data.orthogonal
    data.invariant data.actionMeasurable (data.coefficient output input) (data.weight output input)
    (data.coefficientMeasurable output input) (data.weightMeasurable output input)
    (data.weightNonnegative output input) (data.weightIntegrable output input) (data.domination output input) field

theorem startupDerivativeKernel_entry {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : DerivativeIndex grade) (output input : ℤ) :
    Grad.FullCellKernel.entry (startupDerivativeKernelData admissible family coherent index) output input =
      closedOperatorL2 (startupDerivativeCoefficient admissible family coherent index input (output - input)) := by
  apply ContinuousLinearMap.ext
  intro field
  apply Lp.ext
  filter_upwards [startup_entry_ae (startupDerivativeKernelData admissible family coherent index) output input field,
    closedOperatorL2_ae (startupDerivativeCoefficient admissible family coherent index input (output - input)) field]
    with point original literal
  rw [literal]
  change _ = closedDiskLift
    (startupDerivativeCoefficient admissible family coherent index input (output - input)) point (field point)
  change _ = ∫ _parameter : ℝ, closedDiskLift
    (startupDerivativeCoefficient admissible family coherent index input (output - input)) point (field point)
      ∂Measure.dirac (0 : ℝ) at original
  simpa only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] using original

/-- Complete integer-cell formula for the actual coefficient derivative.
 This is an infinite-cell continuous action, not a finite truncation. -/
theorem startupDerivativeKernel_coordinate {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : DerivativeIndex grade)
    (field : FieldL2 inputDimension openUnitDisk) (output : ℤ) :
    fieldCellProjection outputDimension openUnitDisk output
      (startupDerivativeKernel admissible family coherent index field) =
      ∑' input : ℤ, closedOperatorL2
        (startupDerivativeCoefficient admissible family coherent index input (output - input))
        (fieldCellProjection inputDimension openUnitDisk input field) := by
  rw [startupDerivativeKernel, Grad.FullCellKernel.kernel_coordinate]
  apply tsum_congr
  intro input
  rw [startupDerivativeKernel_entry]

end Grad.GaugeCoefficients.Physical.RadialLedger
