import AAG6ActualCoerciveForm

noncomputable section
set_option maxHeartbeats 800000

namespace Grad.AnnularVariational

open Grad.CartesianState

section Form
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem annularFormValue_test_smul (field test : annularEnergySpace lower length positive) (scalar : ℂ) :
    annularFormValue parameters lower length positive lengthPositive widthHalf widthLength field (scalar • test) =
      (starRingEnd ℂ scalar) *
        annularFormValue parameters lower length positive lengthPositive widthHalf widthLength field test := by
  have base : inner ℂ (scalar • test) field = (starRingEnd ℂ scalar) * inner ℂ test field := by
    change inner ℂ (scalar • test.val) field.val = (starRingEnd ℂ scalar) * inner ℂ test.val field.val
    simp only [inner_smul_left]
  simp only [annularFormValue, map_smul, inner_smul_left, base]
  ring

theorem annularFormValue_field_add (first second test : annularEnergySpace lower length positive) :
    annularFormValue parameters lower length positive lengthPositive widthHalf widthLength (first + second) test =
      annularFormValue parameters lower length positive lengthPositive widthHalf widthLength first test +
        annularFormValue parameters lower length positive lengthPositive widthHalf widthLength second test := by
  simp only [annularFormValue, map_add, inner_add_right]
  ring

theorem annularFormValue_field_smul (field test : annularEnergySpace lower length positive) (scalar : ℂ) :
    annularFormValue parameters lower length positive lengthPositive widthHalf widthLength (scalar • field) test =
      scalar * annularFormValue parameters lower length positive lengthPositive widthHalf widthLength field test := by
  have base : inner ℂ test (scalar • field) = scalar * inner ℂ test field := by
    change inner ℂ test.val (scalar • field.val) = scalar * inner ℂ test.val field.val
    simp only [inner_smul_right]
  simp only [annularFormValue, map_smul, inner_smul_right, base]
  ring

theorem annularFormValue_bound (field test : annularEnergySpace lower length positive) :
    ‖annularFormValue parameters lower length positive lengthPositive widthHalf widthLength field test‖ ≤
      4 * ‖field‖ * ‖test‖ := by
  let derivative := annularEnergyDerivative lower length positive
  let phase := annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength
  have derivativeField := annularEnergyDerivative_bound lower length positive field
  have derivativeTest := annularEnergyDerivative_bound lower length positive test
  have phaseField := annularEnergyPhase_bound parameters lower length positive lengthPositive widthHalf widthLength field
  have phaseTest := annularEnergyPhase_bound parameters lower length positive lengthPositive widthHalf widthLength test
  have first := norm_inner_le_norm (𝕜 := ℂ) test field
  have second : ‖inner ℂ (phase test) (derivative field)‖ ≤ (1 / 2 * ‖test‖) * ‖field‖ :=
    (norm_inner_le_norm (𝕜 := ℂ) (phase test) (derivative field)).trans
      (mul_le_mul phaseTest derivativeField (norm_nonneg (derivative field))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (norm_nonneg test)))
  have third : ‖inner ℂ (derivative test) (phase field)‖ ≤ ‖test‖ * (1 / 2 * ‖field‖) :=
    (norm_inner_le_norm (𝕜 := ℂ) (derivative test) (phase field)).trans
      (mul_le_mul derivativeTest phaseField (norm_nonneg (phase field)) (norm_nonneg test))
  have fourth : ‖inner ℂ (phase test) (phase field)‖ ≤ (1 / 2 * ‖test‖) * (1 / 2 * ‖field‖) :=
    (norm_inner_le_norm (𝕜 := ℂ) (phase test) (phase field)).trans
      (mul_le_mul phaseTest phaseField (norm_nonneg (phase field))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (norm_nonneg test)))
  have triangle := (norm_sub_le
    (inner ℂ test field + inner ℂ (phase test) (derivative field) - inner ℂ (derivative test) (phase field))
    (inner ℂ (phase test) (phase field))).trans
      (add_le_add ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
  change ‖inner ℂ test field + inner ℂ (phase test) (derivative field) -
    inner ℂ (derivative test) (phase field) - inner ℂ (phase test) (phase field)‖ ≤ _
  nlinarith [mul_nonneg (norm_nonneg field) (norm_nonneg test)]

theorem annularForm_abs_bound (field test : annularEnergySpace lower length positive) :
    |annularForm parameters lower length positive lengthPositive widthHalf widthLength field test| ≤
      4 * ‖field‖ * ‖test‖ := by
  rw [annularForm_literal]
  exact (Complex.abs_re_le_norm _).trans
    (annularFormValue_bound parameters lower length positive lengthPositive widthHalf widthLength field test)

end Form

end Grad.AnnularVariational
