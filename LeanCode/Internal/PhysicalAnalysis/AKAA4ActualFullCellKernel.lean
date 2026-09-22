import AKAA3ActualAllocatedCoefficientBounds
import FullCellKernelProof

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.AnalyticWeights.Higher

/-- Full integer-cell realization of one actual Leibniz allocation. The
 Dirac parameter is the identity spatial pullback, with no cell truncation. -/
def startupAllocatedKernelData {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (rank : ℕ) (word : Fin rank → Fin 2) (index : DerivativeIndex grade)
    (allocation : rank + derivativeOrder index ≤ grade) :
    Grad.FullCellKernel.L2KernelData (Measure.dirac (0 : ℝ))
      inputDimension outputDimension openUnitDisk where
  domainMeasurable := openUnitDisk_isOpen.measurableSet
  orthogonal := fun _ => LinearIsometryEquiv.refl ℝ _
  invariant := fun _ => by intro point; rfl
  actionMeasurable := measurable_snd
  coefficient := fun output input pair => closedDiskLift
    (startupAllocatedCoefficient coefficient rank word index input (output - input)) pair.2
  weight := fun output input _ => apRatioConstant L sigma gamma rank *
    ‖weightedDerivative coefficient (output - input) index‖
  coefficientMeasurable := fun output input =>
    (closedOperator_measurable
      (startupAllocatedCoefficient coefficient rank word index input (output - input))).comp_quasiMeasurePreserving
        quasiMeasurePreserving_snd
  weightMeasurable := fun _ _ => measurable_const
  weightNonnegative := fun output input _ => mul_nonneg (apRatioConstant_nonnegative admissible rank)
    (norm_nonneg (weightedDerivative coefficient (output - input) index))
  weightIntegrable := fun _ _ => integrable_const _
  domination := fun output input => by
    filter_upwards [quasiMeasurePreserving_snd.ae (closedOperator_bound
      (startupAllocatedCoefficient coefficient rank word index input (output - input)))] with pair bound
    exact bound.trans (startupAllocatedCoefficient_norm_bound admissible coefficient rank word index allocation input _)
  rowBound := apRatioConstant L sigma gamma rank * ‖coefficient‖
  columnBound := apRatioConstant L sigma gamma rank * ‖coefficient‖
  rowNonnegative := mul_nonneg (apRatioConstant_nonnegative admissible rank) (norm_nonneg _)
  columnNonnegative := mul_nonneg (apRatioConstant_nonnegative admissible rank) (norm_nonneg _)
  rowsSummable := fun output => by
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    exact ((Equiv.subLeft output).summable_iff).mpr
      ((coordinate_norm_summable coefficient.val index).mul_left _)
  columnsSummable := fun input => by
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    exact ((Equiv.subRight input).summable_iff).mpr
      ((coordinate_norm_summable coefficient.val index).mul_left _)
  rows := fun output => by
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    have reindex := (Equiv.subLeft output).tsum_eq (fun shift => apRatioConstant L sigma gamma rank *
      ‖weightedDerivative coefficient shift index‖)
    change (∑' input : ℤ, apRatioConstant L sigma gamma rank *
      ‖weightedDerivative coefficient (output - input) index‖) = _ at reindex
    rw [reindex, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (coordinate_norm_sum_le coefficient.val index)
      (apRatioConstant_nonnegative admissible rank)
  columns := fun input => by
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    have reindex := (Equiv.subRight input).tsum_eq (fun shift => apRatioConstant L sigma gamma rank *
      ‖weightedDerivative coefficient shift index‖)
    change (∑' output : ℤ, apRatioConstant L sigma gamma rank *
      ‖weightedDerivative coefficient (output - input) index‖) = _ at reindex
    rw [reindex, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (coordinate_norm_sum_le coefficient.val index)
      (apRatioConstant_nonnegative admissible rank)

def startupAllocatedKernel {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (rank : ℕ) (word : Fin rank → Fin 2) (index : DerivativeIndex grade)
    (allocation : rank + derivativeOrder index ≤ grade) :=
  Grad.FullCellKernel.kernel (startupAllocatedKernelData admissible coefficient rank word index allocation)

theorem startupAllocatedKernel_norm {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (rank : ℕ) (word : Fin rank → Fin 2) (index : DerivativeIndex grade)
    (allocation : rank + derivativeOrder index ≤ grade) :
    ‖startupAllocatedKernel admissible coefficient rank word index allocation‖ ≤
      apRatioConstant L sigma gamma rank * ‖coefficient‖ := by
  have bound := Grad.FullCellKernel.kernel_norm_le
    (startupAllocatedKernelData admissible coefficient rank word index allocation)
  change ‖startupAllocatedKernel admissible coefficient rank word index allocation‖ ≤
    Real.sqrt ((apRatioConstant L sigma gamma rank * ‖coefficient‖) *
      (apRatioConstant L sigma gamma rank * ‖coefficient‖)) at bound
  simpa only [Real.sqrt_mul_self (mul_nonneg
    (apRatioConstant_nonnegative admissible rank) (norm_nonneg coefficient))] using bound

end Grad.GaugeCoefficients.Physical.RadialLedger
