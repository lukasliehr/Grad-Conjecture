import AKCB4ActualFullOrderedMatrixWeak

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.RepresentedKernel Grad.RepresentedKernel.WeakDerivatives Grad.RepresentedKernel.SpatialProduct

def startupShiftedIndex (baseline index : CartesianMultiIndex) :
    DerivativeIndex (cartesianOrder (index.1+baseline.1,index.2+baseline.2)) :=
  topDerivativeIndex (index.1+baseline.1,index.2+baseline.2)

theorem startupShiftedIndex_zero (baseline : CartesianMultiIndex) :
    derivativeMultiIndex (startupShiftedIndex baseline (0,0)) = baseline := by
  simp [startupShiftedIndex,derivativeMultiIndex_top]

theorem startupShiftedSelected_reserve {rank weight : ℕ}
    (baseline : CartesianMultiIndex) (word : Word rank) (selected : Finset (Fin rank))
    (reserve : cartesianOrder baseline + rank - 1 ≤ weight) :
    derivativeOrder (startupShiftedIndex baseline (selectedIndex word selected)) - 1 ≤ weight := by
  have total := word_direction_count_total selected.card (subword word selected)
  have bounded : selected.card ≤ rank := by simpa only [Fintype.card_fin] using Finset.card_le_univ selected
  change (selectedIndex word selected).1+baseline.1+((selectedIndex word selected).2+baseline.2)-1 ≤ weight
  dsimp [selectedIndex,cartesianOrder] at *
  omega

theorem startupShiftedZero_reserve {rank weight : ℕ} (baseline : CartesianMultiIndex)
    (reserve : cartesianOrder baseline + rank - 1 ≤ weight) :
    derivativeOrder (startupShiftedIndex baseline (0,0)) - 1 ≤ weight := by
  change 0+baseline.1+(0+baseline.2)-1 ≤ weight
  dsimp [cartesianOrder] at reserve
  omega

/-- A fixed pre-existing coefficient derivative is paid by its input
frequency reserve. The underlying native phase and cells are unchanged. -/
theorem startupActualShiftedEntry_reserved {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension order weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (baseline index : CartesianMultiIndex)
    (bound : derivativeOrder (startupShiftedIndex baseline index) - 1 ≤ weight) (fieldIndex : JetIndex order)
    (jet : GraphGrade inputDimension order weight openUnitDisk) (output input : ℤ) :
    operator (startupSingleEntryData
      (shiftedOperatorJet (startupConjugatedCoefficientJet admissible family coherent input (output-input)) baseline) output input) index 0
      (Realization.recoveredDerivative inputDimension order openUnitDisk (fun _ => weight) fieldIndex jet) =
    Grad.FullCellKernel.insertCell outputDimension openUnitDisk output
      (Grad.FullCellKernel.entry (startupDerivativeKernelData admissible family coherent (startupShiftedIndex baseline index)) output input
        (fieldCellProjection inputDimension openUnitDisk input
          (startupReservedDerivative admissible bound fieldIndex jet))) := by
  rw [startupSingleEntry_literal_operator,shiftedOperatorJet_derivative]
  have actual := startupActualEntry_reserved admissible family coherent (startupShiftedIndex baseline index)
    bound fieldIndex jet output input
  rw [startupSingleEntry_literal_operator] at actual
  exact actual

end Grad.CartesianStartup
