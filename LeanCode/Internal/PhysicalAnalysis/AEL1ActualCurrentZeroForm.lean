import AEJ6OnePhysicalHighFormBall

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.AnnularCurrentInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularKernelL2 Grad.AnnularCurrentBoundary Grad.AnnularCurrentEnergy

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)

theorem currentHighFormValue_add_field (first second test : annularEnergySpace lower L positive) :
    currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state (first + second) test =
      currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state first test +
      currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state second test := by
  simp only [currentHighFormValue, currentHighBulkFormValue_add_field, actualCurrentHighBoundaryFormValue_add_field]
  ring

theorem currentHighFormValue_smul_field (scalar : ℂ) (field test : annularEnergySpace lower L positive) :
    currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state (scalar • field) test =
      scalar * currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field test := by
  simp only [currentHighFormValue, currentHighBulkFormValue_smul_field, actualCurrentHighBoundaryFormValue_smul_field]
  ring

theorem currentHighFormValue_add_test (field first second : annularEnergySpace lower L positive) :
    currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field (first + second) =
      currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field first +
      currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field second := by
  simp only [currentHighFormValue, currentHighBulkFormValue_add_test, actualCurrentHighBoundaryFormValue_add_test]
  ring

theorem currentHighFormValue_smul_test (scalar : ℂ) (field test : annularEnergySpace lower L positive) :
    currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field (scalar • test) =
      starRingEnd ℂ scalar * currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field test := by
  simp only [currentHighFormValue, currentHighBulkFormValue_smul_test, actualCurrentHighBoundaryFormValue_smul_test]
  ring

/-- The actual current form restricted to the original closed inner-zero
energy space. Its bulk and outer boundary operators remain unchanged. -/
def currentHighZeroForm :
    annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ]
    annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ :=
  (currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state).bilinearComp
    (annularZeroRealInclusion lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive)
    (annularZeroRealInclusion lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive)

theorem currentHighZeroForm_literal
    (field test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) :
    currentHighZeroForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field test =
      (currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field.val test.val).re :=
  currentHighForm_literal parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field.val test.val

end Grad.AnnularCurrentInverse
