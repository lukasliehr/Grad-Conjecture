import AKBZ15SharpAllocatedKernelBound
import FullCellKernelProof

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators

namespace Grad.OriginalCartesianTameEstimate

open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.AnalyticWeights.Higher
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation

/-- Full integer-cell realization of one actual Leibniz allocation. The
 Dirac parameter is the identity spatial pullback, with no cell truncation. -/
def sharpAllocatedKernelData {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (rank displacement : ℕ) (positive : 0<rank)
    (word : Fin rank → Fin 2) (index : CartesianMultiIndex) :
    Grad.FullCellKernel.L2KernelData (Measure.dirac (0 : ℝ))
      inputDimension outputDimension openUnitDisk where
  domainMeasurable := openUnitDisk_isOpen.measurableSet
  orthogonal := fun _ => LinearIsometryEquiv.refl ℝ _
  invariant := fun _ => by intro point; rfl
  actionMeasurable := measurable_snd
  coefficient := fun output input pair => closedDiskLift
    (sharpAllocatedCoefficient family rank displacement word index input (output - input)) pair.2
  weight := fun output input _ => sharpPhaseConstant L sigma gamma rank *
    ‖weightedDerivative (family (cartesianOrder index+displacement)) (output-input) (sharpCoefficientIndex index displacement)‖
  coefficientMeasurable := fun output input =>
    (closedOperator_measurable
      (sharpAllocatedCoefficient family rank displacement word index input (output - input))).comp_quasiMeasurePreserving
        quasiMeasurePreserving_snd
  weightMeasurable := fun _ _ => measurable_const
  weightNonnegative := fun output input _ => mul_nonneg (sharpPhaseConstant_nonnegative admissible rank)
    (norm_nonneg (weightedDerivative (family (cartesianOrder index+displacement)) (output-input) (sharpCoefficientIndex index displacement)))
  weightIntegrable := fun _ _ => integrable_const _
  domination := fun output input => by
    filter_upwards [quasiMeasurePreserving_snd.ae (closedOperator_bound
      (sharpAllocatedCoefficient family rank displacement word index input (output - input)))] with pair bound
    exact bound.trans (sharpAllocatedCoefficient_norm_bound admissible family coherent rank displacement positive word index input _)
  rowBound := sharpPhaseConstant L sigma gamma rank * ‖family (cartesianOrder index+displacement)‖
  columnBound := sharpPhaseConstant L sigma gamma rank * ‖family (cartesianOrder index+displacement)‖
  rowNonnegative := mul_nonneg (sharpPhaseConstant_nonnegative admissible rank) (norm_nonneg _)
  columnNonnegative := mul_nonneg (sharpPhaseConstant_nonnegative admissible rank) (norm_nonneg _)
  rowsSummable := fun output => by
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    exact ((Equiv.subLeft output).summable_iff).mpr
      ((coordinate_norm_summable (family (cartesianOrder index+displacement)).val (sharpCoefficientIndex index displacement)).mul_left _)
  columnsSummable := fun input => by
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    exact ((Equiv.subRight input).summable_iff).mpr
      ((coordinate_norm_summable (family (cartesianOrder index+displacement)).val (sharpCoefficientIndex index displacement)).mul_left _)
  rows := fun output => by
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    have reindex := (Equiv.subLeft output).tsum_eq (fun shift => sharpPhaseConstant L sigma gamma rank *
      ‖weightedDerivative (family (cartesianOrder index+displacement)) shift (sharpCoefficientIndex index displacement)‖)
    change (∑' input : ℤ, sharpPhaseConstant L sigma gamma rank *
      ‖weightedDerivative (family (cartesianOrder index+displacement)) (output-input) (sharpCoefficientIndex index displacement)‖) = _ at reindex
    rw [reindex, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (coordinate_norm_sum_le (family (cartesianOrder index+displacement)).val (sharpCoefficientIndex index displacement))
      (sharpPhaseConstant_nonnegative admissible rank)
  columns := fun input => by
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    have reindex := (Equiv.subRight input).tsum_eq (fun shift => sharpPhaseConstant L sigma gamma rank *
      ‖weightedDerivative (family (cartesianOrder index+displacement)) shift (sharpCoefficientIndex index displacement)‖)
    change (∑' output : ℤ, sharpPhaseConstant L sigma gamma rank *
      ‖weightedDerivative (family (cartesianOrder index+displacement)) (output-input) (sharpCoefficientIndex index displacement)‖) = _ at reindex
    rw [reindex, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (coordinate_norm_sum_le (family (cartesianOrder index+displacement)).val (sharpCoefficientIndex index displacement))
      (sharpPhaseConstant_nonnegative admissible rank)

def sharpAllocatedKernel {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (rank displacement : ℕ) (positive : 0<rank)
    (word : Fin rank → Fin 2) (index : CartesianMultiIndex) :=
  Grad.FullCellKernel.kernel (sharpAllocatedKernelData admissible family coherent rank displacement positive word index)

theorem sharpAllocatedKernel_norm {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (rank displacement : ℕ) (positive : 0<rank)
    (word : Fin rank → Fin 2) (index : CartesianMultiIndex) :
    ‖sharpAllocatedKernel admissible family coherent rank displacement positive word index‖ ≤
      sharpPhaseConstant L sigma gamma rank * ‖family (cartesianOrder index+displacement)‖ := by
  have bound := Grad.FullCellKernel.kernel_norm_le
    (sharpAllocatedKernelData admissible family coherent rank displacement positive word index)
  change ‖sharpAllocatedKernel admissible family coherent rank displacement positive word index‖ ≤
    Real.sqrt ((sharpPhaseConstant L sigma gamma rank * ‖family (cartesianOrder index+displacement)‖) *
      (sharpPhaseConstant L sigma gamma rank * ‖family (cartesianOrder index+displacement)‖)) at bound
  simpa only [Real.sqrt_mul_self (mul_nonneg
    (sharpPhaseConstant_nonnegative admissible rank) (norm_nonneg (family (cartesianOrder index+displacement))))] using bound

end Grad.OriginalCartesianTameEstimate
