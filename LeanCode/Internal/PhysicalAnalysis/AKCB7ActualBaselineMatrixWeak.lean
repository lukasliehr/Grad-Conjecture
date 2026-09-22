import AKCB6BaselineDerivativeEntries

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2000
open MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.RepresentedKernel Grad.RepresentedKernel.WeakDerivatives Grad.RepresentedKernel.SpatialProduct
open Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

/-- Arbitrary weak derivatives after a fixed coefficient derivative. The
input needs only the current spatial order; all coefficient reserves are
restored on the input before Fourier mixing. -/
theorem startupActualMatrix_baselineWeak {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension order rank weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (baseline : CartesianMultiIndex) (word : Word rank) (bound : rank ≤ order)
    (reserve : cartesianOrder baseline + rank - 1 ≤ weight) (jet : GraphGrade inputDimension order weight openUnitDisk) :
    HasWeakOrderedDerivative outputDimension openUnitDisk rank word
      (startupDerivativeKernel admissible family coherent (startupShiftedIndex baseline (0,0))
        (startupReservedDerivative admissible (startupShiftedZero_reserve baseline reserve) (zeroIndex order) jet))
      (∑ selected : Finset (Fin rank),
        startupDerivativeKernel admissible family coherent (startupShiftedIndex baseline (selectedIndex word selected))
          (startupReservedDerivative admissible (startupShiftedSelected_reserve baseline word selected reserve)
            (startupComplementIndex word bound selected) jet)) := by
  let initial := startupReservedDerivative admissible (startupShiftedZero_reserve baseline reserve) (zeroIndex order) jet
  let coordinate := fun selected : Finset (Fin rank) =>
    startupReservedDerivative admissible (startupShiftedSelected_reserve baseline word selected reserve)
      (startupComplementIndex word bound selected) jet
  let zeroth := startupDerivativeKernelData admissible family coherent (startupShiftedIndex baseline (0,0))
  let derivative := fun selected : Finset (Fin rank) =>
    startupDerivativeKernelData admissible family coherent (startupShiftedIndex baseline (selectedIndex word selected))
  apply startupWeak_from_rows
  intro output
  have fieldsSum := (Grad.FullCellKernel.insertCell outputDimension openUnitDisk output).hasSum
    (startupKernel_row_hasSum zeroth initial output)
  have derivativesSum := hasSum_sum (s := Finset.univ) (fun selected _ =>
    (Grad.FullCellKernel.insertCell outputDimension openUnitDisk output).hasSum
      (startupKernel_row_hasSum (derivative selected) (coordinate selected) output))
  apply startupWeak_hasSum word _ _ _ _ fieldsSum
    (by simpa only [map_sum,derivative,coordinate,startupDerivativeKernel] using derivativesSum)
  intro input
  have weak := startupSingleEntry_orderedWeak
    (shiftedOperatorJet (startupConjugatedCoefficientJet admissible family coherent input (output-input)) baseline) output input word bound jet
  have initialSame := startupActualShiftedEntry_reserved admissible family coherent baseline (0,0)
    (startupShiftedZero_reserve baseline reserve) (zeroIndex order) jet output input
  change operator (startupSingleEntryData
    (shiftedOperatorJet (startupConjugatedCoefficientJet admissible family coherent input (output-input)) baseline) output input)
    (0,0) 0 (base inputDimension order openUnitDisk (fun _ => weight) jet) = _ at initialSame
  rw [initialSame] at weak
  have terms : (∑ selected : Finset (Fin rank),
      operator (startupSingleEntryData
        (shiftedOperatorJet (startupConjugatedCoefficientJet admissible family coherent input (output-input)) baseline) output input)
        (selectedIndex word selected) 0
        (inputDerivative inputDimension order rank weight openUnitDisk bound jet selected (subword word selectedᶜ))) =
      ∑ selected : Finset (Fin rank),
        Grad.FullCellKernel.insertCell outputDimension openUnitDisk output
          (Grad.FullCellKernel.entry (derivative selected) output input
            (fieldCellProjection inputDimension openUnitDisk input (coordinate selected))) := by
    apply Finset.sum_congr rfl
    intro selected _
    rw [startupInputDerivative_recovered]
    exact startupActualShiftedEntry_reserved admissible family coherent baseline (selectedIndex word selected)
      (startupShiftedSelected_reserve baseline word selected reserve) (startupComplementIndex word bound selected) jet output input
  rw [terms] at weak
  exact weak

end Grad.CartesianStartup
