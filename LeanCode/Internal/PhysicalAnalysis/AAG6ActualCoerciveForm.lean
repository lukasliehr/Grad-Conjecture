import AAG5ActualEnergyCoordinates
import ANH18WeakSolve

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.AnnularVariational

open Grad.CartesianState

instance annularEnergy_complexInner (lower length : ℝ) (positive : 0 < lower) :
    InnerProductSpace ℂ (annularEnergySpace lower length positive) :=
  Submodule.innerProductSpace (annularEnergySpace lower length positive)

instance annularEnergy_realInner (lower length : ℝ) (positive : 0 < lower) :
    InnerProductSpace ℝ (annularEnergySpace lower length positive) :=
  InnerProductSpace.rclikeToReal ℂ (annularEnergySpace lower length positive)

instance annularBulk_realInner (lower : ℝ) : InnerProductSpace ℝ (AnnularBulk lower) :=
  InnerProductSpace.rclikeToReal ℂ (AnnularBulk lower)

section Form
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- The expanded AG12 form, using exactly the energy-coordinate pairing and
the actual phase derivative multiplier. Linear in field, conjugate-linear in test. -/
def annularFormValue (field test : annularEnergySpace lower length positive) : ℂ :=
  inner ℂ test field +
    inner ℂ (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test)
      (annularEnergyDerivative lower length positive field) -
    inner ℂ (annularEnergyDerivative lower length positive test)
      (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field) -
    inner ℂ (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test)
      (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)

def annularForm : annularEnergySpace lower length positive →L[ℝ]
    annularEnergySpace lower length positive →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (ContinuousLinearMap.id ℝ (annularEnergySpace lower length positive))
    (ContinuousLinearMap.id ℝ (annularEnergySpace lower length positive)) +
    (innerSL ℝ).bilinearComp (annularEnergyDerivative lower length positive |>.restrictScalars ℝ)
      (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength |>.restrictScalars ℝ) -
    (innerSL ℝ).bilinearComp
      (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength |>.restrictScalars ℝ)
      (annularEnergyDerivative lower length positive |>.restrictScalars ℝ) -
    (innerSL ℝ).bilinearComp
      (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength |>.restrictScalars ℝ)
      (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength |>.restrictScalars ℝ)

theorem annularForm_apply (field test : annularEnergySpace lower length positive) :
    annularForm parameters lower length positive lengthPositive widthHalf widthLength field test =
      inner ℝ field test +
        inner ℝ (annularEnergyDerivative lower length positive field)
          (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test) -
        inner ℝ (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)
          (annularEnergyDerivative lower length positive test) -
        inner ℝ (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)
          (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test) := by
  rfl

theorem annularForm_literal (field test : annularEnergySpace lower length positive) :
    annularForm parameters lower length positive lengthPositive widthHalf widthLength field test =
      (annularFormValue parameters lower length positive lengthPositive widthHalf widthLength field test).re := by
  rw [annularForm_apply]
  simp only [annularFormValue, Complex.sub_re, Complex.add_re]
  change (inner ℂ field test).re +
    (inner ℂ (annularEnergyDerivative lower length positive field)
      (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test)).re -
    (inner ℂ (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)
      (annularEnergyDerivative lower length positive test)).re -
    (inner ℂ (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)
      (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test)).re = _
  have first : (inner ℂ field test).re = (inner ℂ test field).re := inner_re_symm (𝕜 := ℂ) _ _
  have second : (inner ℂ (annularEnergyDerivative lower length positive field)
      (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test)).re =
      (inner ℂ (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test)
        (annularEnergyDerivative lower length positive field)).re := inner_re_symm (𝕜 := ℂ) _ _
  have third : (inner ℂ (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)
      (annularEnergyDerivative lower length positive test)).re =
      (inner ℂ (annularEnergyDerivative lower length positive test)
        (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  have fourth : (inner ℂ (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)
      (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test)).re =
      (inner ℂ (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength test)
        (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  exact congrArg₂ (fun left right : ℝ => left - right)
    (congrArg₂ (fun left right : ℝ => left - right)
      (congrArg₂ (fun left right : ℝ => left + right) first second) third) fourth

theorem annularForm_diagonal (field : annularEnergySpace lower length positive) :
    annularForm parameters lower length positive lengthPositive widthHalf widthLength field field =
      ‖field‖ ^ 2 -
        ‖annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field‖ ^ 2 := by
  rw [annularForm_apply, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  rw [real_inner_comm (annularEnergyDerivative lower length positive field)]
  ring

/-- AG13 with the exact 3/4 coercivity constant on the original energy norm. -/
theorem annularForm_coercive_bound (field : annularEnergySpace lower length positive) :
    (3 / 4 : ℝ) * ‖field‖ ^ 2 ≤
      annularForm parameters lower length positive lengthPositive widthHalf widthLength field field := by
  rw [annularForm_diagonal]
  have phase := annularEnergyPhase_bound parameters lower length positive lengthPositive widthHalf widthLength field
  nlinarith [norm_nonneg field,
    norm_nonneg (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)]

theorem annularForm_isCoercive :
    IsCoercive (annularForm parameters lower length positive lengthPositive widthHalf widthLength) := by
  refine ⟨3 / 4, by norm_num, fun field => ?_⟩
  have estimate := annularForm_coercive_bound parameters lower length positive lengthPositive widthHalf widthLength field
  nlinarith only [estimate]

end Form

end Grad.AnnularVariational
