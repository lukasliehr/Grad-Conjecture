import AKBZ22SameCoarseAndSharpAllocation
import AKAA21FullCellWeakPassage

noncomputable section
set_option maxHeartbeats 1100000
open MeasureTheory MeasureTheory.Measure
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.CartesianState Grad.NonlinearProduct Grad.GenericCarriers

private theorem constantEntry_eq {inputDimension outputDimension : ℕ}
    (data : Grad.FullCellKernel.L2KernelData (Measure.dirac (0:ℝ)) inputDimension outputDimension openUnitDisk)
    (coefficient : C(ClosedDisk,OperatorValue inputDimension outputDimension)) (output input : ℤ)
    (sameCoefficient : data.coefficient output input=fun pair => closedDiskLift coefficient pair.2)
    (sameOrthogonal : data.orthogonal=fun _ => LinearIsometryEquiv.refl ℝ _) :
    Grad.FullCellKernel.entry data output input=closedOperatorL2 coefficient := by
  apply ContinuousLinearMap.ext
  intro field
  apply Lp.ext
  filter_upwards [startup_entry_ae data output input field,closedOperatorL2_ae coefficient field]
    with point action literal
  rw [literal]
  rw [sameCoefficient,sameOrthogonal] at action
  change _ = ∫ _parameter : ℝ, closedDiskLift coefficient point (field point) ∂Measure.dirac (0:ℝ) at action
  simpa only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] using action

theorem sharpAllocatedKernel_entry {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (rank displacement : ℕ) (positive : 0<rank)
    (word : Fin rank → Fin 2) (index : CartesianMultiIndex) (output input : ℤ) :
    Grad.FullCellKernel.entry (sharpAllocatedKernelData admissible family coherent rank displacement positive word index) output input=
    closedOperatorL2 (sharpAllocatedCoefficient family rank displacement word index input (output-input)) :=
  constantEntry_eq _ _ output input rfl rfl

theorem coarseAllocatedKernel_entry {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (rank : ℕ) (word : Fin rank → Fin 2) (index : DerivativeIndex grade)
    (allocated : rank+derivativeOrder index≤grade) (output input : ℤ) :
    Grad.FullCellKernel.entry (startupAllocatedKernelData admissible coefficient rank word index allocated) output input=
    closedOperatorL2 (startupAllocatedCoefficient coefficient rank word index input (output-input)) :=
  constantEntry_eq _ _ output input rfl rfl

end Grad.OriginalCartesianTameEstimate
