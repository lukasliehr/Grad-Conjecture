import AKCB10FullCellDisplacementKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.RepresentedKernel Grad.RepresentedKernel.WeakDerivatives Grad.RepresentedKernel.SpatialProduct
open Grad.WeightedJets.Ordered Grad.WeakTesting Grad.WeakTesting.Commutation

theorem startupWeakOrdered_smul {dimension rank : ℕ} {domain : Set Spatial}
    {word : Word rank} {field derivative : FieldL2 dimension domain}
    (weak : HasWeakOrderedDerivative dimension domain rank word field derivative) (scalar : ℂ) :
    HasWeakOrderedDerivative dimension domain rank word (scalar • field) (scalar • derivative) := by
  intro cell vector test smooth compact supported
  rw [map_smul,map_smul,weak cell vector test smooth compact supported]

/-- The exact original displacement factor multiplies a single matrix entry.
The frequency reserve stays on the input until this identity is applied. -/
theorem startupDisplacementEntry_reserved {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension order weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (baseline index : CartesianMultiIndex) (power : ℕ)
    (bound : derivativeOrder (startupShiftedIndex baseline index)-1≤weight) (fieldIndex : JetIndex order)
    (jet : GraphGrade inputDimension order weight openUnitDisk) (output input : ℤ) :
    startupAxialFrequency L ell (output-input)^power •
      operator (startupSingleEntryData
        (shiftedOperatorJet (startupConjugatedCoefficientJet admissible family coherent input (output-input)) baseline) output input) index 0
        (Realization.recoveredDerivative inputDimension order openUnitDisk (fun _ => weight) fieldIndex jet)=
    Grad.FullCellKernel.insertCell outputDimension openUnitDisk output
      (Grad.FullCellKernel.entry
        (startupDisplacementKernelData admissible family coherent (startupShiftedIndex baseline index) power) output input
        (fieldCellProjection inputDimension openUnitDisk input
          (startupReservedDerivative admissible bound fieldIndex jet))) := by
  rw [startupDisplacementKernel_entry,smul_apply,map_smul,
    startupActualShiftedEntry_reserved admissible family coherent baseline index bound fieldIndex jet output input,
    startupDerivativeKernel_entry]

end Grad.CartesianStartup
