import AEJ4OriginalPhysicalBulkForm
import AEH7ExactBoundaryTermConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.AnnularCurrentEnergy
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularKernelL2 Grad.AnnularCurrentBoundary
open Grad.SourceBoundaryTrace Grad.ActualBoundaryPrimitives Grad.BoundaryKernelAction

attribute [local instance] energyNormed energySeminormed energyRealNormed energyRealModule
local instance boundaryRealInner (parameters : PhaseParameters) :
    InnerProductSpace ℝ (NegativeTrace parameters 0 0 1) :=
  InnerProductSpace.rclikeToReal ℂ (NegativeTrace parameters 0 0 1)

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)

/-- The actual AI14/BF7 form: negative three bulk pairings plus the
unchanged physical outer retained boundary contribution. -/
def currentHighFormValue (field test : annularEnergySpace lower L positive) : ℂ :=
  currentHighBulkFormValue parameters L compact lower positive (lowerHalf.trans (by norm_num))
    lengthPositive widthHalf widthLength state 0 field test +
  actualCurrentHighBoundaryFormValue parameters L compact lower positive lowerHalf
    lengthPositive 0 0 state.outerInverseState field test

def highBoundaryRealForm :
    annularEnergySpace lower L positive →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp
    (((highAngularSubmodule parameters 0 0 1).subtypeL.comp
      (actualCurrentHighBoundaryD parameters L compact lower positive lowerHalf lengthPositive 0 0 state.outerInverseState)).restrictScalars ℝ)
    ((actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0).restrictScalars ℝ)

theorem highBoundaryRealForm_literal (field test : annularEnergySpace lower L positive) :
    highBoundaryRealForm parameters L compact lower positive lowerHalf lengthPositive state field test =
      (actualCurrentHighBoundaryFormValue parameters L compact lower positive lowerHalf
        lengthPositive 0 0 state.outerInverseState field test).re := by
  change (inner ℂ (actualCurrentHighBoundaryD parameters L compact lower positive lowerHalf
    lengthPositive 0 0 state.outerInverseState field).val
    (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test)).re = _
  exact inner_re_symm (𝕜 := ℂ) _ _

def currentHighForm :=
  currentHighBulkForm parameters L compact lower positive (lowerHalf.trans (by norm_num))
    lengthPositive widthHalf widthLength state 0 +
  highBoundaryRealForm parameters L compact lower positive lowerHalf lengthPositive state

theorem currentHighForm_literal (field test : annularEnergySpace lower L positive) :
    currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field test =
      (currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field test).re := by
  simp only [currentHighForm, currentHighFormValue, add_apply, currentHighBulkForm_literal,
    highBoundaryRealForm_literal, Complex.add_re]

def currentHighErrorConstant : ℝ :=
  highBulkErrorConstant parameters L compact 0 + actualCurrentHighBoundaryFormConstant parameters L compact 0 0

theorem currentHighErrorConstant_nonnegative : 0 ≤ currentHighErrorConstant parameters L compact :=
  add_nonneg (highBulkErrorConstant_nonnegative parameters L compact 0)
    (actualCurrentHighBoundaryFormConstant_nonnegative parameters L compact 0 0)

theorem currentHighFormValue_difference_bound (field test : annularEnergySpace lower L positive) :
    ‖currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field test -
      circularHighBulkFormValue parameters L lower positive (lowerHalf.trans (by norm_num))
        lengthPositive widthHalf widthLength 0 field test‖ ≤
    currentHighErrorConstant parameters L compact * state.val.errorBudget 1 * ‖field‖ * ‖test‖ := by
  have bulk := highBulkErrorFormValue_base_bound parameters L compact lower positive (lowerHalf.trans (by norm_num))
    lengthPositive widthHalf widthLength state field test
  have boundary := actualCurrentHighBoundaryForm_bound parameters L compact lower positive lowerHalf
    lengthPositive 0 0 state.outerInverseState field test
  have boundary' : ‖actualCurrentHighBoundaryFormValue parameters L compact lower positive lowerHalf
      lengthPositive 0 0 state.outerInverseState field test‖ ≤
    actualCurrentHighBoundaryFormConstant parameters L compact 0 0 * state.val.errorBudget 1 * ‖field‖ * ‖test‖ := boundary
  rw [currentHighFormValue, add_sub_right_comm, ← highBulkErrorFormValue_eq_sub]
  exact (norm_add_le _ _).trans ((add_le_add bulk boundary').trans_eq (by unfold currentHighErrorConstant highBulkErrorConstant; ring))

/-- Uniform operator-norm difference from the literal circular bulk form.
The reference identity with the energy form is supplied separately by AIA. -/
theorem currentHighForm_difference_norm :
    ‖currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state -
      circularHighBulkForm parameters L lower positive (lowerHalf.trans (by norm_num)) lengthPositive widthHalf widthLength 0‖ ≤
      currentHighErrorConstant parameters L compact * state.val.errorBudget 1 := by
  have budgetNonnegative := Grad.GaugeCoefficients.Physical.Allocation.physicalBudget_nonnegative
    parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8
  have nonnegative := mul_nonneg (currentHighErrorConstant_nonnegative parameters L compact) budgetNonnegative
  apply ContinuousLinearMap.opNorm_le_bound _ nonnegative
  intro field
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg nonnegative (norm_nonneg field))
  intro test
  simp only [sub_apply, currentHighForm_literal, circularHighBulkForm_literal, ← Complex.sub_re, Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans
    (currentHighFormValue_difference_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field test)

end Grad.AnnularCurrentEnergy
