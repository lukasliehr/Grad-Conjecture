import AEF9UniformTiltSolutionBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace Grad.AnnularUniformBoundary

open Grad.CartesianState Grad.AnnularVariational
open Grad.AnnularTiltedReference

section Inverse

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- Uniform full-data constant for the independent four-slot forcing and
incoming boundary datum. -/
def annularTiltUniformInverseConstant (length : ℝ) : ℝ :=
  16 * (5 + uniformOuterTraceConstant length) +
    65 * uniformInnerLiftConstant length

theorem annularTiltUniformInverseConstant_nonnegative :
    0 ≤ annularTiltUniformInverseConstant length := by
  unfold annularTiltUniformInverseConstant
  exact add_nonneg
    (mul_nonneg (by norm_num) (add_nonneg (by norm_num)
      (uniformOuterTraceConstant_nonnegative length)))
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

/-- The exact already-constructed complex-linear solution map has uniform
operator norm on every collar `lower ≤ 1/2`. -/
theorem annularTiltVariationalLinear_uniform_bound
    (data : AnnularForcing lower × AnnularBoundary) :
    ‖annularTiltVariationalLinear parameters lower length positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive widthHalf widthLength data‖ ≤
      annularTiltUniformInverseConstant length * ‖data‖ := by
  have energy := annularTiltVariationalSolution_uniform_bound parameters lower length positive
    lowerHalf lengthPositive widthHalf widthLength data.1 data.2
  have sourceSize := uniformAnnularForcingSize_bound lower length data.1
  have coefficientNonnegative : 0 ≤ 5 + uniformOuterTraceConstant length :=
    add_nonneg (by norm_num) (uniformOuterTraceConstant_nonnegative length)
  have sourceBound : uniformAnnularForcingSize lower length data.1 ≤
      (5 + uniformOuterTraceConstant length) * ‖data‖ :=
    sourceSize.trans (mul_le_mul_of_nonneg_left (norm_fst_le data) coefficientNonnegative)
  have innerBound : uniformInnerLiftConstant length * ‖data.2‖ ≤
      uniformInnerLiftConstant length * ‖data‖ :=
    mul_le_mul_of_nonneg_left (norm_snd_le data) (Real.sqrt_nonneg _)
  change ‖annularTiltVariationalSolution parameters lower length positive
    (lowerHalf.trans_lt (by norm_num)) lengthPositive widthHalf widthLength data.1 data.2‖ ≤ _
  unfold annularTiltUniformInverseConstant
  nlinarith only [energy, sourceBound, innerBound]

/-- Uniform bounded realization of the same accepted tilted inverse. -/
def annularTiltVariationalUniformInverse :
    (AnnularForcing lower × AnnularBoundary) →L[ℂ]
      annularEnergySpace lower length positive :=
  (annularTiltVariationalLinear parameters lower length positive
    (lowerHalf.trans_lt (by norm_num)) lengthPositive widthHalf widthLength).mkContinuous
      (annularTiltUniformInverseConstant length)
      (annularTiltVariationalLinear_uniform_bound parameters lower length positive
        lowerHalf lengthPositive widthHalf widthLength)

@[simp] theorem annularTiltVariationalUniformInverse_apply
    (data : AnnularForcing lower × AnnularBoundary) :
    annularTiltVariationalUniformInverse parameters lower length positive lowerHalf
      lengthPositive widthHalf widthLength data =
    annularTiltVariationalSolution parameters lower length positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive widthHalf widthLength data.1 data.2 := rfl

/-- Changing only the proved continuity constant does not change the inverse. -/
theorem annularTiltVariationalUniformInverse_eq_fixed :
    annularTiltVariationalUniformInverse parameters lower length positive lowerHalf
      lengthPositive widthHalf widthLength =
    annularTiltVariationalInverse parameters lower length positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive widthHalf widthLength := by
  apply ContinuousLinearMap.ext
  intro data
  rfl

end Inverse

end Grad.AnnularUniformBoundary
