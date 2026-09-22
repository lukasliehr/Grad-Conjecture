import BKB26ActualForceKernels

noncomputable section

set_option maxHeartbeats 1800000

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace

theorem NegativeTrace.ext_coefficient {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (first second : NegativeTrace parameters angular cell dimension)
    (same : ∀ mode, negativeTraceCoefficient parameters angular cell first mode =
      negativeTraceCoefficient parameters angular cell second mode) :
    first = second := by
  apply Subtype.ext
  funext mode
  have equality := congrArg (fun value : ComplexEuclidean dimension =>
    (negativeTraceWeight parameters angular cell mode : ℂ) • value) (same mode)
  unfold negativeTraceCoefficient at equality
  simpa only [smul_smul, mul_inv_cancel₀
    (Complex.ofReal_ne_zero.mpr
      (negativeTraceWeight_pos parameters angular cell mode).ne'), one_smul] using equality

theorem negativeTraceCoefficient_norm_le {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (field : NegativeTrace parameters angular cell dimension)
    (mode : ℤ × ℤ) :
    ‖negativeTraceCoefficient parameters angular cell field mode‖ ≤
      (negativeTraceWeight parameters angular cell mode)⁻¹ * ‖field‖ := by
  unfold negativeTraceCoefficient
  rw [norm_smul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (negativeTraceWeight_pos parameters angular cell mode).le]
  exact mul_le_mul_of_nonneg_left
    (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) field mode)
    (inv_nonneg.mpr (negativeTraceWeight_pos parameters angular cell mode).le)

def fullKernelActionPairTerm
    {inputDimension middleDimension outputDimension : ℕ}
    {parameters : PhaseParameters} (angular cell : ℕ)
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension)
    (field : NegativeTrace parameters angular cell inputDimension)
    (mode : ℤ × ℤ) (pair : (ℤ × ℤ) × (ℤ × ℤ)) :
    ComplexEuclidean outputDimension :=
  outer.entry pair.1 (twoFrequencyTranslation pair.1 mode)
    (inner.entry pair.2
      (twoFrequencyTranslation pair.2 (twoFrequencyTranslation pair.1 mode))
      (negativeTraceCoefficient parameters angular cell field
        (twoFrequencyTranslation pair.2 (twoFrequencyTranslation pair.1 mode))))

theorem fullKernelActionPairTerm_coefficient
    {inputDimension middleDimension outputDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension)
    (field : NegativeTrace parameters angular cell inputDimension)
    (mode : ℤ × ℤ) (pair : (ℤ × ℤ) × (ℤ × ℤ)) :
    fullKernelActionPairTerm angular cell outer inner field mode pair =
      negativeTraceCoefficient parameters angular cell
        (fullNegativeShiftAction parameters angular cell outer pair.1
          (fullNegativeShiftAction parameters angular cell inner pair.2 field)) mode := by
  rw [fullNegativeShiftAction_coefficient,
    fullNegativeShiftAction_coefficient]
  rfl

theorem fullKernelActionPairTerm_norm_le
    {inputDimension middleDimension outputDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension)
    (field : NegativeTrace parameters angular cell inputDimension)
    (mode : ℤ × ℤ) (pair : (ℤ × ℤ) × (ℤ × ℤ)) :
    ‖fullKernelActionPairTerm angular cell outer inner field mode pair‖ ≤
      (negativeTraceWeight parameters angular cell mode)⁻¹ *
        (negativeShiftCost parameters angular cell pair.1 * outer.entryNorm pair.1) *
        (negativeShiftCost parameters angular cell pair.2 * inner.entryNorm pair.2) *
          ‖field‖ := by
  rw [fullKernelActionPairTerm_coefficient]
  apply (negativeTraceCoefficient_norm_le parameters angular cell _ mode).trans
  have outerApply := ContinuousLinearMap.le_opNorm
    (fullNegativeShiftAction parameters angular cell outer pair.1)
    (fullNegativeShiftAction parameters angular cell inner pair.2 field)
  have innerApply := ContinuousLinearMap.le_opNorm
    (fullNegativeShiftAction parameters angular cell inner pair.2) field
  have outerNorm := fullNegativeShiftAction_norm_le parameters angular cell outer pair.1
  have innerNorm := fullNegativeShiftAction_norm_le parameters angular cell inner pair.2
  calc
    (negativeTraceWeight parameters angular cell mode)⁻¹ *
        ‖fullNegativeShiftAction parameters angular cell outer pair.1
          (fullNegativeShiftAction parameters angular cell inner pair.2 field)‖
        ≤ (negativeTraceWeight parameters angular cell mode)⁻¹ *
            (‖fullNegativeShiftAction parameters angular cell outer pair.1‖ *
              ‖fullNegativeShiftAction parameters angular cell inner pair.2 field‖) :=
          mul_le_mul_of_nonneg_left outerApply
            (inv_nonneg.mpr (negativeTraceWeight_pos parameters angular cell mode).le)
    _ ≤ (negativeTraceWeight parameters angular cell mode)⁻¹ *
          ((negativeShiftCost parameters angular cell pair.1 * outer.entryNorm pair.1) *
            (negativeShiftCost parameters angular cell pair.2 * inner.entryNorm pair.2 *
              ‖field‖)) := by
      apply mul_le_mul_of_nonneg_left _
        (inv_nonneg.mpr (negativeTraceWeight_pos parameters angular cell mode).le)
      exact mul_le_mul outerNorm
        (innerApply.trans (mul_le_mul_of_nonneg_right innerNorm (norm_nonneg field)))
        (norm_nonneg _)
        (mul_nonneg (negativeShiftCost_nonnegative parameters angular cell pair.1)
          (fullKernelEntryNorm_nonnegative outer pair.1))
    _ = _ := by ring

theorem fullKernelActionPairTerm_summable
    {inputDimension middleDimension outputDimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (outer : FullTwoFrequencyKernel parameters middleDimension outputDimension)
    (inner : FullTwoFrequencyKernel parameters inputDimension middleDimension)
    (field : NegativeTrace parameters angular cell inputDimension)
    (mode : ℤ × ℤ) :
    Summable (fullKernelActionPairTerm angular cell outer inner field mode) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun pair => norm_nonneg _)
    (fullKernelActionPairTerm_norm_le parameters angular cell outer inner field mode)
  have product := (outer.moments (angular + cell + 1)).mul_of_nonneg
    (inner.moments (angular + cell + 1))
    (fun shift => mul_nonneg
      (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters shift)
        (pow_nonneg (annularFrequency_pos shift).le _))
      (fullKernelEntryNorm_nonnegative outer shift))
    (fun shift => mul_nonneg
      (mul_nonneg (boundaryCoefficientPhaseCost_nonnegative parameters shift)
        (pow_nonneg (annularFrequency_pos shift).le _))
      (fullKernelEntryNorm_nonnegative inner shift))
  apply (product.mul_left
    ((negativeTraceWeight parameters angular cell mode)⁻¹ * ‖field‖)).congr
  intro pair
  unfold negativeShiftCost
  ring

end Grad.BoundaryKernelAction
