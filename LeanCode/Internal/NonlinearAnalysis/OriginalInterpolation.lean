import ProductInterface

noncomputable section

namespace Grad.NonlinearProduct

open Grad.ClosedJets Grad.CartesianState Grad.FourierGrade Grad.COR12Extension Grad.FourierInterpolation

def originalInterpolationConstant (low middle high : ℕ) : ℝ :=
  sameGradeConstant middle *
    sameGradeConstant low ^ (1 - interpolationTheta low middle high) *
      sameGradeConstant high ^ interpolationTheta low middle high

theorem originalInterpolationConstant_nonnegative (low middle high : ℕ) :
    0 ≤ originalInterpolationConstant low middle high := by
  exact mul_nonneg (mul_nonneg (sameGradeConstant_nonnegative _)
    (Real.rpow_nonneg (sameGradeConstant_nonnegative _) _))
      (Real.rpow_nonneg (sameGradeConstant_nonnegative _) _)

/-- P17 in the literal original Cartesian norm. The single phase-weighted
extension is chosen before the grades, and no analytic width changes. -/
theorem original_grade_interpolation {dimension : ℕ} {parameters : PhaseParameters}
    {low middle high : ℕ} (lowMiddle : low < middle) (middleHigh : middle < high)
    (field : ACore parameters dimension) :
    originalGradeNorm middle field ≤ originalInterpolationConstant low middle high *
      (originalGradeNorm low field ^ (1 - interpolationTheta low middle high) *
        originalGradeNorm high field ^ interpolationTheta low middle high) := by
  let extended := weightedFourierExtension parameters field
  have reverseBound : originalGradeNorm middle field ≤
      sameGradeConstant middle * ‖coreToGrade middle extended‖ := by
    have bound := weightedFourierRetraction_norm_le parameters extended middle
    simpa only [extended, weightedFourierRetraction_extension, originalGradeNorm] using bound
  have lowBound := weightedFourierExtension_norm_le parameters field low
  have highBound := weightedFourierExtension_norm_le parameters field high
  have thetaPositive := interpolationTheta_pos lowMiddle middleHigh
  have thetaLessOne := interpolationTheta_lt_one lowMiddle middleHigh
  calc
    originalGradeNorm middle field ≤ sameGradeConstant middle * ‖coreToGrade middle extended‖ := reverseBound
    _ ≤ sameGradeConstant middle *
        (‖coreToGrade low extended‖ ^ (1 - interpolationTheta low middle high) *
          ‖coreToGrade high extended‖ ^ interpolationTheta low middle high) :=
      mul_le_mul_of_nonneg_left (jCore_grade_norm_interpolation lowMiddle middleHigh extended)
        (sameGradeConstant_nonnegative _)
    _ ≤ sameGradeConstant middle *
        ((sameGradeConstant low * originalGradeNorm low field) ^ (1 - interpolationTheta low middle high) *
          (sameGradeConstant high * originalGradeNorm high field) ^ interpolationTheta low middle high) := by
      apply mul_le_mul_of_nonneg_left _ (sameGradeConstant_nonnegative _)
      apply mul_le_mul
      · exact Real.rpow_le_rpow (norm_nonneg _) lowBound (sub_nonneg.mpr thetaLessOne.le)
      · exact Real.rpow_le_rpow (norm_nonneg _) highBound thetaPositive.le
      · exact Real.rpow_nonneg (norm_nonneg _) _
      · exact Real.rpow_nonneg (mul_nonneg (sameGradeConstant_nonnegative _)
          (originalGradeNorm_nonnegative _ _)) _
    _ = _ := by
      rw [Real.mul_rpow (sameGradeConstant_nonnegative _) (originalGradeNorm_nonnegative _ _),
        Real.mul_rpow (sameGradeConstant_nonnegative _) (originalGradeNorm_nonnegative _ _)]
      unfold originalInterpolationConstant
      ring

end Grad.NonlinearProduct
