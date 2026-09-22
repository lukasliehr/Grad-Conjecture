import AEJ1ActualEliminatedDifference

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace Grad.AnnularCurrentEnergy
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularKernelL2

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact) (power : ℕ)

/-- The actual eliminated high bulk form, with the physical opposite-phase
derivative test and the literal homogeneous eight-input packet. -/
def currentHighBulkFormValue (field test : annularEnergySpace lower L positive) : ℂ :=
  -inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test)
    (eliminatedBulkAction parameters L compact lower positive bounded state power
      (highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength field))

def circularHighBulkFormValue (field test : annularEnergySpace lower L positive) : ℂ :=
  -inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test)
    (circularEliminatedBulkAction parameters L lower positive bounded power
      (highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength field))

def highBulkErrorFormValue (field test : annularEnergySpace lower L positive) : ℂ :=
  -inner ℂ (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test)
    (eliminatedBulkErrorAction parameters L compact lower positive bounded state power
      (highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength field))

theorem highBulkErrorFormValue_eq_sub (field test : annularEnergySpace lower L positive) :
    highBulkErrorFormValue parameters L compact lower positive bounded lengthPositive widthHalf widthLength state power field test =
      currentHighBulkFormValue parameters L compact lower positive bounded lengthPositive widthHalf widthLength state power field test -
        circularHighBulkFormValue parameters L lower positive bounded lengthPositive widthHalf widthLength power field test := by
  unfold highBulkErrorFormValue currentHighBulkFormValue circularHighBulkFormValue
  rw [eliminatedBulkErrorAction_eq_sub]
  simp only [sub_apply, inner_sub_right]
  abel

theorem highBulkErrorFormValue_bound (field test : annularEnergySpace lower L positive) :
    ‖highBulkErrorFormValue parameters L compact lower positive bounded lengthPositive widthHalf widthLength state power field test‖ ≤
      (5 * eliminatedBulkErrorConstant parameters L compact power * (4 + 2 * |L|)) *
        state.val.errorBudget power * ‖field‖ * ‖test‖ := by
  let packet := highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength field
  let testPacket := highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test
  have errorBound := eliminatedBulkErrorAction_bound parameters L compact lower positive bounded state power packet
  have inputBound : ‖packet‖ ≤ (4 + 2 * |L|) * ‖field‖ :=
    highEightEnergyPacket_bound parameters lower L positive lengthPositive widthHalf widthLength field
  have testBound : ‖testPacket‖ ≤ 5 * ‖test‖ :=
    highEnergyTestPacket_bound parameters lower L positive lengthPositive widthHalf widthLength test
  have errorNonnegative : 0 ≤ eliminatedBulkErrorConstant parameters L compact power * state.val.errorBudget power :=
    mul_nonneg (eliminatedBulkErrorConstant_nonnegative parameters L compact power) (Grad.GaugeCoefficients.Physical.Allocation.physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon (power + 7))
  have outputBound := errorBound.trans (mul_le_mul_of_nonneg_left inputBound errorNonnegative)
  change ‖-inner ℂ testPacket (eliminatedBulkErrorAction parameters L compact lower positive bounded state power packet)‖ ≤ _
  rw [norm_neg]
  calc
    _ ≤ ‖testPacket‖ * ‖eliminatedBulkErrorAction parameters L compact lower positive bounded state power packet‖ := norm_inner_le_norm _ _
    _ ≤ (5 * ‖test‖) * (eliminatedBulkErrorConstant parameters L compact power * state.val.errorBudget power *
        ((4 + 2 * |L|) * ‖field‖)) :=
      mul_le_mul testBound outputBound (norm_nonneg _) (by positivity)
    _ = _ := by ring

end Grad.AnnularCurrentEnergy
