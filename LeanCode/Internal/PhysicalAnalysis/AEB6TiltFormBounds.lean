import AEB5LiteralTiltCoordinates

noncomputable section
set_option maxHeartbeats 800000

namespace Grad.AnnularTiltedReference

open Grad.CartesianState Grad.AnnularVariational

section Form
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem annularTiltEnergyPhase_bound_one (field : annularEnergySpace lower length positive) :
    ‖annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field‖ ≤
      1 * ‖field‖ := by
  apply (annularTiltEnergyPhase_bound parameters lower length positive lengthPositive widthHalf widthLength field).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg field)
  exact (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem annularTiltFormValue_test_smul (field test : annularEnergySpace lower length positive) (scalar : ℂ) :
    annularTiltFormValue parameters lower length positive lengthPositive widthHalf widthLength field (scalar • test) =
      (starRingEnd ℂ scalar) *
        annularTiltFormValue parameters lower length positive lengthPositive widthHalf widthLength field test := by
  have base : inner ℂ (scalar • test) field = (starRingEnd ℂ scalar) * inner ℂ test field := by
    change inner ℂ (scalar • test.val) field.val = (starRingEnd ℂ scalar) * inner ℂ test.val field.val
    simp only [inner_smul_left]
  simp only [annularTiltFormValue, map_smul, inner_smul_left, base]
  ring

theorem annularTiltFormValue_field_add (first second test : annularEnergySpace lower length positive) :
    annularTiltFormValue parameters lower length positive lengthPositive widthHalf widthLength (first + second) test =
      annularTiltFormValue parameters lower length positive lengthPositive widthHalf widthLength first test +
        annularTiltFormValue parameters lower length positive lengthPositive widthHalf widthLength second test := by
  simp only [annularTiltFormValue, map_add, inner_add_right]
  ring

theorem annularTiltFormValue_field_smul (field test : annularEnergySpace lower length positive) (scalar : ℂ) :
    annularTiltFormValue parameters lower length positive lengthPositive widthHalf widthLength (scalar • field) test =
      scalar * annularTiltFormValue parameters lower length positive lengthPositive widthHalf widthLength field test := by
  have base : inner ℂ test (scalar • field) = scalar * inner ℂ test field := by
    change inner ℂ test.val (scalar • field.val) = scalar * inner ℂ test.val field.val
    simp only [inner_smul_right]
  simp only [annularTiltFormValue, map_smul, inner_smul_right, base]
  ring

theorem annularTiltFormValue_bound (field test : annularEnergySpace lower length positive) :
    ‖annularTiltFormValue parameters lower length positive lengthPositive widthHalf widthLength field test‖ ≤
      4 * ‖field‖ * ‖test‖ := by
  let derivative := annularEnergyDerivative lower length positive
  let phase := annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength
  have derivativeField := annularEnergyDerivative_bound lower length positive field
  have derivativeTest := annularEnergyDerivative_bound lower length positive test
  have phaseField := annularTiltEnergyPhase_bound_one parameters lower length positive lengthPositive widthHalf widthLength field
  have phaseTest := annularTiltEnergyPhase_bound_one parameters lower length positive lengthPositive widthHalf widthLength test
  have first := norm_inner_le_norm (𝕜 := ℂ) test field
  have second : ‖inner ℂ (phase test) (derivative field)‖ ≤ (1 * ‖test‖) * ‖field‖ :=
    (norm_inner_le_norm (𝕜 := ℂ) (phase test) (derivative field)).trans
      (mul_le_mul phaseTest derivativeField (norm_nonneg (derivative field))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg test)))
  have third : ‖inner ℂ (derivative test) (phase field)‖ ≤ ‖test‖ * (1 * ‖field‖) :=
    (norm_inner_le_norm (𝕜 := ℂ) (derivative test) (phase field)).trans
      (mul_le_mul derivativeTest phaseField (norm_nonneg (phase field)) (norm_nonneg test))
  have fourth : ‖inner ℂ (phase test) (phase field)‖ ≤ (1 * ‖test‖) * (1 * ‖field‖) :=
    (norm_inner_le_norm (𝕜 := ℂ) (phase test) (phase field)).trans
      (mul_le_mul phaseTest phaseField (norm_nonneg (phase field))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg test)))
  have triangle := (norm_sub_le
    (inner ℂ test field + inner ℂ (phase test) (derivative field) - inner ℂ (derivative test) (phase field))
    (inner ℂ (phase test) (phase field))).trans
      (add_le_add ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
  change ‖inner ℂ test field + inner ℂ (phase test) (derivative field) -
    inner ℂ (derivative test) (phase field) - inner ℂ (phase test) (phase field)‖ ≤ _
  nlinarith [mul_nonneg (norm_nonneg field) (norm_nonneg test)]

theorem annularTiltForm_abs_bound (field test : annularEnergySpace lower length positive) :
    |annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength field test| ≤
      4 * ‖field‖ * ‖test‖ := by
  rw [annularTiltForm_literal]
  exact (Complex.abs_re_le_norm _).trans
    (annularTiltFormValue_bound parameters lower length positive lengthPositive widthHalf widthLength field test)

end Form

end Grad.AnnularTiltedReference
