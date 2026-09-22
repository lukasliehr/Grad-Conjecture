import AKAA21FullCellWeakPassage

noncomputable section

set_option maxHeartbeats 1600000

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators ContDiff Topology

namespace Grad.CartesianStartup

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.Allocation
open Grad.RepresentedKernel Grad.RepresentedKernel.WeakDerivatives Grad.RepresentedKernel.SpatialProduct
open Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

def startupFirstCoefficientIndex (direction : Fin 2) : DerivativeIndex 1 :=
  if direction = 0 then ⟨(⟨1, by omega⟩, ⟨0, by omega⟩), by decide⟩
  else ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by decide⟩

theorem startupFirstCoefficientIndex_multi (direction : Fin 2) :
    derivativeMultiIndex (startupFirstCoefficientIndex direction) = startupFirstIndex direction := by
  fin_cases direction <;> rfl

theorem startupFirstCoefficientIndex_order (direction : Fin 2) :
    derivativeOrder (startupFirstCoefficientIndex direction) = 1 := by
  fin_cases direction <;> rfl

theorem startupDerivativeCoefficient_low {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : DerivativeIndex grade)
    (low : derivativeOrder index ≤ 1) (input shift : ℤ) :
    startupDerivativeCoefficient admissible family coherent index input shift =
      smoothOperatorDerivative (startupConjugatedCoefficientJet admissible family coherent input shift)
        (derivativeMultiIndex index) := by
  rw [startupDerivativeCoefficient, Nat.sub_eq_zero_of_le low, pow_zero, Complex.ofReal_one, inv_one, one_smul]

theorem startupActualEntry_low {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : DerivativeIndex grade)
    (low : derivativeOrder index ≤ 1) (output input : ℤ) (field : StartupL2 inputDimension) :
    operator (startupSingleEntryData
      (startupConjugatedCoefficientJet admissible family coherent input (output - input)) output input)
      (derivativeMultiIndex index) 0 field =
    Grad.FullCellKernel.insertCell outputDimension openUnitDisk output
      (Grad.FullCellKernel.entry (startupDerivativeKernelData admissible family coherent index) output input
        (fieldCellProjection inputDimension openUnitDisk input field)) := by
  rw [startupSingleEntry_literal_operator, startupDerivativeKernel_entry, startupDerivativeCoefficient_low admissible family coherent index low]

/-- Genuine first weak derivatives of the actual phase-conjugated complete
 matrix kernel. Both terms act on the unreserved L2 carrier; the equation
 follows from fixed-entry weak calculus and convergent full-cell row sums. -/
theorem startupActualMatrix_firstWeak {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension order weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (direction : Fin 2) (bound : 1 ≤ order)
    (field : Grad.WeightedJets.GraphGrade inputDimension order weight openUnitDisk) :
    HasWeakOrderedDerivative outputDimension openUnitDisk 1 (startupFirstWord direction)
      (startupDerivativeKernel admissible family coherent zeroDerivativeIndex
        (Grad.WeightedJets.base inputDimension order openUnitDisk (fun _ => weight) field))
      (startupDerivativeKernel admissible family coherent zeroDerivativeIndex
        (orderedDerivative inputDimension order 1 openUnitDisk (fun _ => weight) bound field (startupFirstWord direction)) +
      startupDerivativeKernel admissible family coherent (startupFirstCoefficientIndex direction)
        (Grad.WeightedJets.base inputDimension order openUnitDisk (fun _ => weight) field)) := by
  let base := Grad.WeightedJets.base inputDimension order openUnitDisk (fun _ => weight) field
  let derivative := orderedDerivative inputDimension order 1 openUnitDisk (fun _ => weight) bound field (startupFirstWord direction)
  let zeroth := startupDerivativeKernelData admissible family coherent zeroDerivativeIndex
  let first := startupDerivativeKernelData admissible family coherent (startupFirstCoefficientIndex direction)
  apply startupWeak_from_rows
  intro output
  have fieldsSum := (Grad.FullCellKernel.insertCell outputDimension openUnitDisk output).hasSum
    (startupKernel_row_hasSum zeroth base output)
  have derivativesSum := ((Grad.FullCellKernel.insertCell outputDimension openUnitDisk output).hasSum
    (startupKernel_row_hasSum zeroth derivative output)).add
    ((Grad.FullCellKernel.insertCell outputDimension openUnitDisk output).hasSum
      (startupKernel_row_hasSum first base output))
  rw [map_add, map_add]
  apply startupWeak_hasSum (startupFirstWord direction) _ _ _ _ fieldsSum derivativesSum
  intro input
  have weak := startupSingleEntry_firstWeak
    (startupConjugatedCoefficientJet admissible family coherent input (output - input)) output input direction bound field
  rw [← startupFirstCoefficientIndex_multi direction] at weak
  have zeroLow : derivativeOrder zeroDerivativeIndex ≤ 1 := by decide
  have firstLow : derivativeOrder (startupFirstCoefficientIndex direction) ≤ 1 :=
    (startupFirstCoefficientIndex_order direction).le
  change HasWeakOrderedDerivative outputDimension openUnitDisk 1 (startupFirstWord direction)
    (operator (startupSingleEntryData
      (startupConjugatedCoefficientJet admissible family coherent input (output - input)) output input)
      (derivativeMultiIndex zeroDerivativeIndex) 0 base)
    (operator (startupSingleEntryData
      (startupConjugatedCoefficientJet admissible family coherent input (output - input)) output input)
      (derivativeMultiIndex zeroDerivativeIndex) 0 derivative +
    operator (startupSingleEntryData
      (startupConjugatedCoefficientJet admissible family coherent input (output - input)) output input)
      (derivativeMultiIndex (startupFirstCoefficientIndex direction)) 0 base) at weak
  rw [startupActualEntry_low admissible family coherent zeroDerivativeIndex zeroLow,
    startupActualEntry_low admissible family coherent zeroDerivativeIndex zeroLow,
    startupActualEntry_low admissible family coherent (startupFirstCoefficientIndex direction) firstLow] at weak
  exact weak

end Grad.CartesianStartup
