import AKCB3ActualReservedMatrixEntry

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2000
open MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.RepresentedKernel Grad.RepresentedKernel.WeakDerivatives Grad.RepresentedKernel.SpatialProduct
open Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

def startupComplementIndex {rank order : ℕ} (word : Word rank) (bound : rank ≤ order)
    (selected : Finset (Fin rank)) : JetIndex order :=
  wordIndex (show selectedᶜ.card ≤ order from by
    have cardinality : selectedᶜ.card ≤ rank := by simpa only [Fintype.card_fin] using Finset.card_le_univ selectedᶜ
    exact cardinality.trans bound)
      (subword word selectedᶜ)

theorem startupInputDerivative_recovered {dimension order rank weight : ℕ}
    (word : Word rank) (bound : rank ≤ order)
    (jet : GraphGrade dimension order weight openUnitDisk) (selected : Finset (Fin rank)) :
    inputDerivative dimension order rank weight openUnitDisk bound jet selected (subword word selectedᶜ) =
      Realization.recoveredDerivative dimension order openUnitDisk (fun _ => weight)
        (startupComplementIndex word bound selected) jet := by
  apply orderedDerivative_apply

/-- Arbitrary ordered weak derivatives of the actual full phase-conjugated
matrix. Only q spatial derivatives of the input are required. The cell
reserve is restored before each coefficient kernel acts. -/
theorem startupActualMatrix_orderedWeak {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension order rank weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (word : Word rank) (bound : rank ≤ order)
    (reserve : rank - 1 ≤ weight) (jet : GraphGrade inputDimension order weight openUnitDisk) :
    HasWeakOrderedDerivative outputDimension openUnitDisk rank word
      (startupDerivativeKernel admissible family coherent zeroDerivativeIndex
        (base inputDimension order openUnitDisk (fun _ => weight) jet))
      (∑ selected : Finset (Fin rank),
        startupDerivativeKernel admissible family coherent (startupSelectedCoefficientIndex word selected)
          (startupReservedDerivative admissible (startupSelectedCoefficientIndex_reserve word selected reserve)
            (startupComplementIndex word bound selected) jet)) := by
  let initial := base inputDimension order openUnitDisk (fun _ => weight) jet
  let coordinate := fun selected : Finset (Fin rank) =>
    startupReservedDerivative admissible (startupSelectedCoefficientIndex_reserve word selected reserve)
      (startupComplementIndex word bound selected) jet
  let zeroth := startupDerivativeKernelData admissible family coherent zeroDerivativeIndex
  let derivative := fun selected : Finset (Fin rank) =>
    startupDerivativeKernelData admissible family coherent (startupSelectedCoefficientIndex word selected)
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
    (startupConjugatedCoefficientJet admissible family coherent input (output-input)) output input word bound jet
  have initialSame := startupActualEntry_low admissible family coherent zeroDerivativeIndex
    (by decide : derivativeOrder zeroDerivativeIndex ≤ 1) output input initial
  change operator (startupSingleEntryData
    (startupConjugatedCoefficientJet admissible family coherent input (output-input)) output input)
    (0,0) 0 initial = _ at initialSame
  rw [initialSame] at weak
  have terms : (∑ selected : Finset (Fin rank),
      operator (startupSingleEntryData
        (startupConjugatedCoefficientJet admissible family coherent input (output-input)) output input)
        (selectedIndex word selected) 0
        (inputDerivative inputDimension order rank weight openUnitDisk bound jet selected (subword word selectedᶜ))) =
      ∑ selected : Finset (Fin rank),
        Grad.FullCellKernel.insertCell outputDimension openUnitDisk output
          (Grad.FullCellKernel.entry (derivative selected) output input
            (fieldCellProjection inputDimension openUnitDisk input (coordinate selected))) := by
    apply Finset.sum_congr rfl
    intro selected _
    rw [startupInputDerivative_recovered,← startupSelectedCoefficientIndex_multi word selected]
    exact startupActualEntry_reserved admissible family coherent (startupSelectedCoefficientIndex word selected)
      (startupSelectedCoefficientIndex_reserve word selected reserve) (startupComplementIndex word bound selected) jet output input
  rw [terms] at weak
  exact weak

end Grad.CartesianStartup
