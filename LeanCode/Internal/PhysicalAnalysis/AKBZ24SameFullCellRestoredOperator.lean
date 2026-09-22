import AKBZ23LiteralAllocatedKernelEntries

noncomputable section
set_option maxHeartbeats 1400000
open MeasureTheory
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.CartesianState Grad.NonlinearProduct Grad.GenericCarriers Grad.CartesianStartup

theorem sharpCoefficientIndex_allocation (rank : ℕ) (index : CartesianMultiIndex) :
    rank+derivativeOrder (sharpCoefficientIndex index rank)≤cartesianOrder index+rank := by
  rw [sharpCoefficientIndex_order]
  omega

/-- Exact equality of the already accepted coarse full-cell operator with
the sharp d-sum, applied to the same original weighted derivatives. All
input frequencies are restored before summation and all integer cells remain. -/
theorem originalRestoredOperator_eq_sharpSum {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (rank inputRank : ℕ) (positive : 0<rank)
    (word : Fin rank → Fin 2) (index : CartesianMultiIndex)
    (parameters : PhaseParameters) (field : ACore parameters inputDimension) (inputWord : CartesianWord inputRank) :
    startupAllocatedKernel admissible (family (cartesianOrder index+rank)) rank word
      (sharpCoefficientIndex index rank) (sharpCoefficientIndex_allocation rank index)
      (originalMixedDerivativeCarrier parameters admissible field inputRank (rank-1) inputWord)=
    ∑ displacement : Fin rank,
      sharpAllocatedKernel admissible family coherent rank (displacement.val+1) positive word index
        (originalMixedDerivativeCarrier parameters admissible field inputRank (rank-(displacement.val+1)) inputWord) := by
  apply (Grad.FullCellKernel.coordinateIsometry outputDimension openUnitDisk).injective
  apply lp.ext
  funext output
  rw [Grad.FullCellKernel.coordinateIsometry_apply,Grad.FullCellKernel.coordinateIsometry_apply,_root_.map_sum]
  have left := startupKernel_row_hasSum
    (startupAllocatedKernelData admissible (family (cartesianOrder index+rank)) rank word
      (sharpCoefficientIndex index rank) (sharpCoefficientIndex_allocation rank index))
    (originalMixedDerivativeCarrier parameters admissible field inputRank (rank-1) inputWord) output
  have right := hasSum_sum (s:=Finset.univ) (fun (displacement : Fin rank) _ =>
    startupKernel_row_hasSum (sharpAllocatedKernelData admissible family coherent rank (displacement.val+1) positive word index)
      (originalMixedDerivativeCarrier parameters admissible field inputRank (rank-(displacement.val+1)) inputWord) output)
  have term (input : ℤ) :
      Grad.FullCellKernel.entry
        (startupAllocatedKernelData admissible (family (cartesianOrder index+rank)) rank word
          (sharpCoefficientIndex index rank) (sharpCoefficientIndex_allocation rank index)) output input
        (fieldCellProjection inputDimension openUnitDisk input
          (originalMixedDerivativeCarrier parameters admissible field inputRank (rank-1) inputWord))=
      ∑ displacement : Fin rank,
        Grad.FullCellKernel.entry (sharpAllocatedKernelData admissible family coherent rank (displacement.val+1) positive word index) output input
          (fieldCellProjection inputDimension openUnitDisk input
            (originalMixedDerivativeCarrier parameters admissible field inputRank (rank-(displacement.val+1)) inputWord)) := by
    rw [coarseAllocatedKernel_entry,originalMixedDerivativeCarrier_coordinate]
    simp_rw [sharpAllocatedKernel_entry,originalMixedDerivativeCarrier_coordinate]
    simpa only [originalMixedDerivativeCoordinate,Complex.ofReal_pow] using
      (sharpAllocatedOperator_sameCoarse family coherent rank positive word index input (output-input)
        (closedContinuousToDiskL2 (closedDerivative (phaseWeightedJet parameters input (field.val input)) inputRank inputWord))).symm
  exact (left.congr_fun (fun input => (term input).symm)).unique right

end Grad.OriginalCartesianTameEstimate
