import AKCB9ActualCellDisplacementCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open MeasureTheory MeasureTheory.Measure
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

/-- Full signed-cell p-th displacement kernel. The extra p frequencies are
paid on the coefficient before summation; the original width is unchanged. -/
def startupDisplacementKernelData {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : DerivativeIndex grade) (power : ℕ) :
    Grad.FullCellKernel.L2KernelData (Measure.dirac (0:ℝ)) inputDimension outputDimension openUnitDisk :=
  { startupDerivativeKernelData admissible family coherent (startupCellReserveIndex power index) with
    coefficient := fun output input pair => closedDiskLift
      (startupDisplacementCoefficient admissible family coherent index power input (output-input)) pair.2
    coefficientMeasurable := fun output input =>
      (closedOperator_measurable
        (startupDisplacementCoefficient admissible family coherent index power input (output-input))).comp_quasiMeasurePreserving
          quasiMeasurePreserving_snd
    domination := fun output input => by
      filter_upwards [quasiMeasurePreserving_snd.ae (closedOperator_bound
        (startupDisplacementCoefficient admissible family coherent index power input (output-input)))] with pair bound
      exact bound.trans (startupDisplacementCoefficient_bound admissible family coherent index power input (output-input)) }

def startupDisplacementKernel {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : DerivativeIndex grade) (power : ℕ) :=
  Grad.FullCellKernel.kernel (startupDisplacementKernelData admissible family coherent index power)

theorem startupDisplacementKernel_norm {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : DerivativeIndex grade) (power : ℕ) :
    ‖startupDisplacementKernel admissible family coherent index power‖≤
      startupDerivativeConstant L sigma gamma (startupCellReserveIndex power index) * ‖family (grade+power)‖ := by
  have bound := Grad.FullCellKernel.kernel_norm_le (startupDisplacementKernelData admissible family coherent index power)
  change ‖startupDisplacementKernel admissible family coherent index power‖≤Real.sqrt
    ((startupDerivativeConstant L sigma gamma (startupCellReserveIndex power index) * ‖family (grade+power)‖) *
      (startupDerivativeConstant L sigma gamma (startupCellReserveIndex power index) * ‖family (grade+power)‖)) at bound
  simpa only [Real.sqrt_mul_self (mul_nonneg
    (startupDerivativeConstant_nonnegative admissible (startupCellReserveIndex power index)) (norm_nonneg _))] using bound

/-- Exact action of an entry of the displacement kernel on the original disk L2. -/
theorem startupDisplacementKernel_entry {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : DerivativeIndex grade) (power : ℕ) (output input : ℤ) :
    Grad.FullCellKernel.entry (startupDisplacementKernelData admissible family coherent index power) output input=
      startupAxialFrequency L ell (output-input)^power •
        closedOperatorL2 (startupDerivativeCoefficient admissible family coherent index input (output-input)) := by
  have literal : Grad.FullCellKernel.entry (startupDisplacementKernelData admissible family coherent index power) output input=
      closedOperatorL2 (startupDisplacementCoefficient admissible family coherent index power input (output-input)) := by
    apply ContinuousLinearMap.ext
    intro field
    apply Lp.ext
    filter_upwards [startup_entry_ae (startupDisplacementKernelData admissible family coherent index power) output input field,
      closedOperatorL2_ae (startupDisplacementCoefficient admissible family coherent index power input (output-input)) field]
      with point action actual
    rw [actual]
    change _ = ∫ _parameter : ℝ, closedDiskLift
      (startupDisplacementCoefficient admissible family coherent index power input (output-input)) point (field point)
        ∂Measure.dirac (0:ℝ) at action
    simpa only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] using action
  rw [literal,startupDisplacementCoefficient,closedOperatorL2_smul]

end Grad.CartesianStartup
