import AEF7UniformBWeightedLift

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.AnnularUniformBoundary

open Grad.CartesianState Grad.AnnularVariational
open Grad.AnnularTiltedReference

/-- The exact tilted forcing size with the fixed terminal-half-collar trace
constant.  It depends on `length`, but not on the inner radius. -/
def uniformAnnularForcingSize (lower length : ℝ) (source : AnnularForcing lower) : ℝ :=
  3 * ‖source.1‖ + ‖source.2.1‖ + ‖source.2.2.1‖ +
    uniformOuterTraceConstant length * ‖source.2.2.2‖

theorem uniformAnnularForcingSize_nonnegative (lower length : ℝ) (source : AnnularForcing lower) :
    0 ≤ uniformAnnularForcingSize lower length source := by
  unfold uniformAnnularForcingSize
  exact add_nonneg
    (add_nonneg (add_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (norm_nonneg _))
      (norm_nonneg _))
    (mul_nonneg (uniformOuterTraceConstant_nonnegative length) (norm_nonneg _))

section Functional

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- Uniform bound for the literal four-slot tilted functional.  The only
collar-dependent estimate in the original proof was the outer trace; here it
is replaced by the equal completed fixed-half-collar trace. -/
theorem annularTiltFunctionalValue_uniform_bound (source : AnnularForcing lower)
    (test : annularEnergySpace lower length positive) :
    ‖annularTiltFunctionalValue parameters lower length positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive widthHalf widthLength source test‖ ≤
      uniformAnnularForcingSize lower length source * ‖test‖ := by
  have first := (norm_inner_le_norm (𝕜 := ℂ)
    (annularTiltSourceTest parameters lower length positive lengthPositive widthHalf widthLength test)
      source.1).trans
    (mul_le_mul_of_nonneg_right
      (annularTiltSourceTest_bound parameters lower length positive lengthPositive
        widthHalf widthLength test) (norm_nonneg source.1))
  have second := (norm_inner_le_norm (𝕜 := ℂ)
    (annularEnergyD lower length positive test) source.2.1).trans
    (mul_le_mul_of_nonneg_right (annularEnergyD_bound lower length positive test)
      (norm_nonneg source.2.1))
  have third := (norm_inner_le_norm (𝕜 := ℂ)
    (annularEnergyCell lower length positive test) source.2.2.1).trans
    (mul_le_mul_of_nonneg_right (annularEnergyCell_bound lower length positive test)
      (norm_nonneg source.2.2.1))
  have fourth := (norm_inner_le_norm (𝕜 := ℂ)
    (annularEnergyTrace lower length positive (lowerHalf.trans_lt (by norm_num))
      lengthPositive 1 test) source.2.2.2).trans
    (mul_le_mul_of_nonneg_right
      (annularEnergyOuterTrace_uniform_bound lower length positive lowerHalf
        (lowerHalf.trans_lt (by norm_num)) lengthPositive test)
      (norm_nonneg source.2.2.2))
  have triangle := (norm_sub_le
    (inner ℂ (annularTiltSourceTest parameters lower length positive lengthPositive
        widthHalf widthLength test) source.1 -
      inner ℂ (annularEnergyD lower length positive test) source.2.1 -
      inner ℂ (annularEnergyCell lower length positive test) source.2.2.1)
    (inner ℂ (annularEnergyTrace lower length positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive 1 test) source.2.2.2)).trans
      (add_le_add ((norm_sub_le _ _).trans
        (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
  unfold annularTiltFunctionalValue uniformAnnularForcingSize
  nlinarith only [triangle, first, second, third, fourth]

theorem uniformAnnularForcingSize_bound (source : AnnularForcing lower) :
    uniformAnnularForcingSize lower length source ≤
      (5 + uniformOuterTraceConstant length) * ‖source‖ := by
  have first : ‖source.1‖ ≤ ‖source‖ := norm_fst_le source
  have second : ‖source.2.1‖ ≤ ‖source‖ :=
    (norm_fst_le source.2).trans (norm_snd_le source)
  have third : ‖source.2.2.1‖ ≤ ‖source‖ :=
    (norm_fst_le source.2.2).trans ((norm_snd_le source.2).trans (norm_snd_le source))
  have fourth : ‖source.2.2.2‖ ≤ ‖source‖ :=
    (norm_snd_le source.2.2).trans ((norm_snd_le source.2).trans (norm_snd_le source))
  have traceBound := mul_le_mul_of_nonneg_left fourth
    (uniformOuterTraceConstant_nonnegative length)
  unfold uniformAnnularForcingSize
  nlinarith only [first, second, third, traceBound]

end Functional

end Grad.AnnularUniformBoundary
