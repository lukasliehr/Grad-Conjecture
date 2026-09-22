import AEL1ActualCurrentZeroForm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.AnnularCurrentInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularCurrentEnergy

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)

/-- Testing the SAME actual current form with z and iz recovers its full
complex equation from its real variational equation. -/
theorem currentHighForm_real_implies_complex
    (field : annularEnergySpace lower L positive)
    (source : annularEnergySpace lower L positive → ℂ)
    (sourceImaginary : ∀ test, source (Complex.I • test) = starRingEnd ℂ Complex.I * source test)
    (realEquation : ∀ test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive,
      currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field test.val =
        (source test.val).re)
    (test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) :
    currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field test.val =
      source test.val := by
  have realLaw (point : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) :
      (currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field point.val).re =
        (source point.val).re :=
    (currentHighForm_literal parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field point.val).symm.trans
      (realEquation point)
  apply Complex.ext (realLaw test)
  have imaginaryLaw := realLaw (Complex.I • test)
  have formLaw := congrArg Complex.re
    (currentHighFormValue_smul_test parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state Complex.I field test.val)
  have sourceLaw := congrArg Complex.re (sourceImaginary test.val)
  have equality := formLaw.symm.trans (imaginaryLaw.trans sourceLaw)
  simpa using equality

/-- No imaginary residual is lost when the test space is restricted by the
original inner trace, since that closed space is a complex subspace. -/
theorem currentHighForm_real_iff_complex
    (field : annularEnergySpace lower L positive)
    (source : annularEnergySpace lower L positive → ℂ)
    (sourceImaginary : ∀ test, source (Complex.I • test) = starRingEnd ℂ Complex.I * source test) :
    (∀ test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive,
      currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field test.val =
        (source test.val).re) ↔
    (∀ test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive,
      currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field test.val = source test.val) := by
  constructor
  · exact fun equation test => currentHighForm_real_implies_complex parameters L compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state field source sourceImaginary equation test
  · intro equation test
    exact (currentHighForm_literal parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field test.val).trans
      (congrArg Complex.re (equation test))

end Grad.AnnularCurrentInverse
