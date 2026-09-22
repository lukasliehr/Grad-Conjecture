import AEB2ActualTiltMultiplier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.AnnularTiltedReference
open Grad.CartesianState Grad.AnnularVariational

section Form
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- The expanded BF7 form, using exactly the energy-coordinate pairing and
the actual phase derivative multiplier. Linear in field, conjugate-linear in test. -/
def annularTiltFormValue (field test : annularEnergySpace lower length positive) : ℂ :=
  inner ℂ test field +
    inner ℂ (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test)
      (annularEnergyDerivative lower length positive field) -
    inner ℂ (annularEnergyDerivative lower length positive test)
      (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field) -
    inner ℂ (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test)
      (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)

def annularTiltForm : annularEnergySpace lower length positive →L[ℝ]
    annularEnergySpace lower length positive →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (ContinuousLinearMap.id ℝ (annularEnergySpace lower length positive))
    (ContinuousLinearMap.id ℝ (annularEnergySpace lower length positive)) +
    (innerSL ℝ).bilinearComp (annularEnergyDerivative lower length positive |>.restrictScalars ℝ)
      (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength |>.restrictScalars ℝ) -
    (innerSL ℝ).bilinearComp
      (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength |>.restrictScalars ℝ)
      (annularEnergyDerivative lower length positive |>.restrictScalars ℝ) -
    (innerSL ℝ).bilinearComp
      (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength |>.restrictScalars ℝ)
      (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength |>.restrictScalars ℝ)

theorem annularTiltForm_apply (field test : annularEnergySpace lower length positive) :
    annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength field test =
      inner ℝ field test +
        inner ℝ (annularEnergyDerivative lower length positive field)
          (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test) -
        inner ℝ (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)
          (annularEnergyDerivative lower length positive test) -
        inner ℝ (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)
          (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test) := by
  rfl

theorem annularTiltForm_literal (field test : annularEnergySpace lower length positive) :
    annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength field test =
      (annularTiltFormValue parameters lower length positive lengthPositive widthHalf widthLength field test).re := by
  rw [annularTiltForm_apply]
  simp only [annularTiltFormValue, Complex.sub_re, Complex.add_re]
  change (inner ℂ field test).re +
    (inner ℂ (annularEnergyDerivative lower length positive field)
      (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test)).re -
    (inner ℂ (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)
      (annularEnergyDerivative lower length positive test)).re -
    (inner ℂ (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)
      (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test)).re = _
  have first : (inner ℂ field test).re = (inner ℂ test field).re := inner_re_symm (𝕜 := ℂ) _ _
  have second : (inner ℂ (annularEnergyDerivative lower length positive field)
      (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test)).re =
      (inner ℂ (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test)
        (annularEnergyDerivative lower length positive field)).re := inner_re_symm (𝕜 := ℂ) _ _
  have third : (inner ℂ (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)
      (annularEnergyDerivative lower length positive test)).re =
      (inner ℂ (annularEnergyDerivative lower length positive test)
        (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  have fourth : (inner ℂ (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)
      (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test)).re =
      (inner ℂ (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test)
        (annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  exact congrArg₂ (fun left right : ℝ => left - right)
    (congrArg₂ (fun left right : ℝ => left - right)
      (congrArg₂ (fun left right : ℝ => left + right) first second) third) fourth

theorem annularTiltForm_diagonal (field : annularEnergySpace lower length positive) :
    annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength field field =
      ‖field‖ ^ 2 -
        ‖annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field‖ ^ 2 := by
  rw [annularTiltForm_apply, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  rw [real_inner_comm (annularEnergyDerivative lower length positive field)]
  ring

/-- BF10 with the exact 1/16 coercivity constant on the original energy norm. -/
theorem annularTiltForm_coercive_bound (field : annularEnergySpace lower length positive) :
    (1 / 16 : ℝ) * ‖field‖ ^ 2 ≤
      annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength field field := by
  rw [annularTiltForm_diagonal]
  have phase := pow_le_pow_left₀ (norm_nonneg _)
    (annularTiltEnergyPhase_bound parameters lower length positive lengthPositive widthHalf widthLength field) 2
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15 / 16)] at phase
  nlinarith only [phase]

theorem annularTiltForm_isCoercive :
    IsCoercive (annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength) := by
  refine ⟨1 / 16, by norm_num, fun field => ?_⟩
  have estimate := annularTiltForm_coercive_bound parameters lower length positive lengthPositive widthHalf widthLength field
  nlinarith only [estimate]

end Form

end Grad.AnnularTiltedReference
