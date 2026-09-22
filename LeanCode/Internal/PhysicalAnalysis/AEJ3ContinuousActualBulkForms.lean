import AEJ2ActualHighBulkForms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.AnnularCurrentEnergy
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularKernelL2

local instance energyNormed (lower L : ℝ) (positive : 0 < lower) :
    NormedAddCommGroup (annularEnergySpace lower L positive) := inferInstance

local instance energySeminormed (lower L : ℝ) (positive : 0 < lower) :
    SeminormedAddCommGroup (annularEnergySpace lower L positive) :=
  (energyNormed lower L positive).toSeminormedAddCommGroup

local instance energyRealNormed (lower L : ℝ) (positive : 0 < lower) :
    NormedSpace ℝ (annularEnergySpace lower L positive) :=
  (annularEnergy_realInner lower L positive).toNormedSpace

local instance energyRealModule (lower L : ℝ) (positive : 0 < lower) :
    Module ℝ (annularEnergySpace lower L positive) :=
  (energyRealNormed lower L positive).toModule

local instance bulkRealInner (lower : ℝ) : InnerProductSpace ℝ (DivisionRow 3 lower) :=
  InnerProductSpace.rclikeToReal ℂ (DivisionRow 3 lower)

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact) (power : ℕ)

/-- Real bilinear realization of the physical bulk pairing. -/
def highBulkPairing (action : DivisionRow 8 lower →L[ℂ] DivisionRow 3 lower) :
    annularEnergySpace lower L positive →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ :=
  -(innerSL ℝ).bilinearComp
    ((action.comp (highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength)).restrictScalars ℝ)
    ((highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength).restrictScalars ℝ)

theorem highBulkPairing_literal (action : DivisionRow 8 lower →L[ℂ] DivisionRow 3 lower)
    (field test : annularEnergySpace lower L positive) :
    highBulkPairing parameters L lower positive lengthPositive widthHalf widthLength action field test =
      (-inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test)
        (action (highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength field))).re := by
  change -(inner ℂ (action (highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength field))
    (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test)).re = _
  exact congrArg Neg.neg (inner_re_symm (𝕜 := ℂ) _ _)

def currentHighBulkForm := highBulkPairing parameters L lower positive lengthPositive widthHalf widthLength
  (eliminatedBulkAction parameters L compact lower positive bounded state power)

def circularHighBulkForm := highBulkPairing parameters L lower positive lengthPositive widthHalf widthLength
  (circularEliminatedBulkAction parameters L lower positive bounded power)

def highBulkErrorForm := highBulkPairing parameters L lower positive lengthPositive widthHalf widthLength
  (eliminatedBulkErrorAction parameters L compact lower positive bounded state power)

theorem currentHighBulkForm_literal (field test : annularEnergySpace lower L positive) :
    currentHighBulkForm parameters L compact lower positive bounded lengthPositive widthHalf widthLength state power field test =
      (currentHighBulkFormValue parameters L compact lower positive bounded lengthPositive widthHalf widthLength state power field test).re :=
  highBulkPairing_literal parameters L lower positive lengthPositive widthHalf widthLength _ field test

theorem circularHighBulkForm_literal (field test : annularEnergySpace lower L positive) :
    circularHighBulkForm parameters L lower positive bounded lengthPositive widthHalf widthLength power field test =
      (circularHighBulkFormValue parameters L lower positive bounded lengthPositive widthHalf widthLength power field test).re :=
  highBulkPairing_literal parameters L lower positive lengthPositive widthHalf widthLength _ field test

theorem highBulkErrorForm_literal (field test : annularEnergySpace lower L positive) :
    highBulkErrorForm parameters L compact lower positive bounded lengthPositive widthHalf widthLength state power field test =
      (highBulkErrorFormValue parameters L compact lower positive bounded lengthPositive widthHalf widthLength state power field test).re :=
  highBulkPairing_literal parameters L lower positive lengthPositive widthHalf widthLength _ field test

theorem highBulkErrorForm_eq_sub :
    highBulkErrorForm parameters L compact lower positive bounded lengthPositive widthHalf widthLength state power =
      currentHighBulkForm parameters L compact lower positive bounded lengthPositive widthHalf widthLength state power -
        circularHighBulkForm parameters L lower positive bounded lengthPositive widthHalf widthLength power := by
  ext field test
  simp only [sub_apply, highBulkErrorForm_literal, currentHighBulkForm_literal,
    circularHighBulkForm_literal, highBulkErrorFormValue_eq_sub, Complex.sub_re]

def highBulkErrorConstant : ℝ := 5 * eliminatedBulkErrorConstant parameters L compact power * (4 + 2 * |L|)

theorem highBulkErrorConstant_nonnegative : 0 ≤ highBulkErrorConstant parameters L compact power :=
  mul_nonneg (mul_nonneg (by norm_num) (eliminatedBulkErrorConstant_nonnegative parameters L compact power)) (by positivity)

/-- Operator-norm perturbation bound on the full completed energy space;
the constant is chosen before the inner radius and physical state. -/
theorem highBulkErrorForm_norm :
    ‖highBulkErrorForm parameters L compact lower positive bounded lengthPositive widthHalf widthLength state power‖ ≤
      highBulkErrorConstant parameters L compact power * state.val.errorBudget power := by
  have budgetNonnegative := Grad.GaugeCoefficients.Physical.Allocation.physicalBudget_nonnegative
    parameters state.val.val.field state.val.val.rho state.val.val.epsilon (power + 7)
  have constantNonnegative := highBulkErrorConstant_nonnegative parameters L compact power
  have nonnegative : 0 ≤ highBulkErrorConstant parameters L compact power * state.val.errorBudget power :=
    mul_nonneg constantNonnegative budgetNonnegative
  apply ContinuousLinearMap.opNorm_le_bound _ nonnegative
  intro field
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg nonnegative (norm_nonneg field))
  intro test
  rw [highBulkErrorForm_literal, Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans
    (highBulkErrorFormValue_bound parameters L compact lower positive bounded lengthPositive widthHalf widthLength state power field test)

end Grad.AnnularCurrentEnergy
