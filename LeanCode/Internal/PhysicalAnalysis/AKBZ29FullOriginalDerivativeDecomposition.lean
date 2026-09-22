import AKBZ28ActualLeibnizRestoredIdentity

noncomputable section
set_option maxHeartbeats 1400000
open MeasureTheory
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.CartesianState Grad.NonlinearProduct Grad.GenericCarriers Grad.CartesianStartup

def originalLeibnizKernelData {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension grade : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (index : DerivativeIndex grade) (split : DerivativeSplit index) :=
  startupAllocatedKernelData admissible
    (family (cartesianOrder (rawSplitIndex index split)+phaseSplitOrder index split))
    (phaseSplitOrder index split) (phaseSplitWord index split)
    (sharpCoefficientIndex (rawSplitIndex index split) (phaseSplitOrder index split))
    (sharpCoefficientIndex_allocation (phaseSplitOrder index split) (rawSplitIndex index split))

def originalLeibnizKernel {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension grade : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (index : DerivativeIndex grade) (split : DerivativeSplit index) :=
  Grad.FullCellKernel.kernel (originalLeibnizKernelData admissible family index split)

/-- Complete actual conjugated matrix derivative on every signed cell:
its normalization is restored on the SAME weighted input before the exact
finite Leibniz expansion. This is the bridge from the actual weak derivative
operator to the one-high allocation estimates. -/
theorem originalFullDerivative_eq_allocations {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension grade : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : DerivativeIndex grade)
    (parameters : PhaseParameters) (field : ACore parameters inputDimension)
    (inputRank : ℕ) (inputWord : CartesianWord inputRank) :
    startupDerivativeKernel admissible family coherent index
      (originalMixedDerivativeCarrier parameters admissible field inputRank (derivativeOrder index-1) inputWord)=
    ∑ split : DerivativeSplit index,(splitMultiplicity index split:ℂ) •
      originalLeibnizKernel admissible family index split
        (originalMixedDerivativeCarrier parameters admissible field inputRank (phaseSplitOrder index split-1) inputWord) := by
  apply (Grad.FullCellKernel.coordinateIsometry outputDimension openUnitDisk).injective
  apply lp.ext
  funext output
  rw [Grad.FullCellKernel.coordinateIsometry_apply,Grad.FullCellKernel.coordinateIsometry_apply,_root_.map_sum]
  simp_rw [map_smul]
  have left := startupKernel_row_hasSum (startupDerivativeKernelData admissible family coherent index)
    (originalMixedDerivativeCarrier parameters admissible field inputRank (derivativeOrder index-1) inputWord) output
  have right := hasSum_sum (s:=Finset.univ) (fun (split : DerivativeSplit index) _ =>
    (startupKernel_row_hasSum (originalLeibnizKernelData admissible family index split)
      (originalMixedDerivativeCarrier parameters admissible field inputRank (phaseSplitOrder index split-1) inputWord) output).const_smul
      (splitMultiplicity index split:ℂ))
  have term (input : ℤ) :
      Grad.FullCellKernel.entry (startupDerivativeKernelData admissible family coherent index) output input
        (fieldCellProjection inputDimension openUnitDisk input
          (originalMixedDerivativeCarrier parameters admissible field inputRank (derivativeOrder index-1) inputWord))=
      ∑ split : DerivativeSplit index,(splitMultiplicity index split:ℂ) •
        Grad.FullCellKernel.entry (originalLeibnizKernelData admissible family index split) output input
          (fieldCellProjection inputDimension openUnitDisk input
            (originalMixedDerivativeCarrier parameters admissible field inputRank (phaseSplitOrder index split-1) inputWord)) := by
    rw [startupDerivativeKernel_entry,originalMixedDerivativeCarrier_coordinate]
    simp_rw [originalLeibnizKernelData,coarseAllocatedKernel_entry,originalMixedDerivativeCarrier_coordinate]
    simpa only [originalLeibnizCoefficient,originalMixedDerivativeCoordinate,Complex.ofReal_pow] using
      originalDerivativeOperator_restored admissible family coherent index input (output-input)
        (closedContinuousToDiskL2 (closedDerivative (phaseWeightedJet parameters input (field.val input)) inputRank inputWord))
  exact (left.congr_fun (fun input => (term input).symm)).unique right

end Grad.OriginalCartesianTameEstimate
