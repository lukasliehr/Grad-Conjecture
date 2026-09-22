import AEB8ConstructedTiltReferenceInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.AnnularTiltedReference
open Grad.CartesianState Grad.AnnularVariational Grad.AnnularReconstruction

section Functional
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

def annularTiltSourceTest : annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower :=
  annularEnergyDerivative lower length positive +
    annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength +
    annularEnergyRadial lower length positive

theorem annularTiltSourceTest_bound (field : annularEnergySpace lower length positive) :
    ‖annularTiltSourceTest parameters lower length positive lengthPositive widthHalf widthLength field‖ ≤ 3 * ‖field‖ := by
  have first := annularEnergyDerivative_bound lower length positive field
  have second := annularTiltEnergyPhase_bound_one parameters lower length positive lengthPositive widthHalf widthLength field
  have third := annularEnergyRadial_bound lower length positive field
  have triangle := (norm_add_le
    (annularEnergyDerivative lower length positive field +
      annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)
    (annularEnergyRadial lower length positive field)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  change ‖annularEnergyDerivative lower length positive field +
    annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field +
    annularEnergyRadial lower length positive field‖ ≤ _
  nlinarith [norm_nonneg field]

/-- The literal tilted reference functional in normalized coordinates. Source signs and the actual outer trace are retained. -/
def annularTiltFunctionalValue (source : AnnularForcing lower) (test : annularEnergySpace lower length positive) : ℂ :=
  inner ℂ (annularTiltSourceTest parameters lower length positive lengthPositive widthHalf widthLength test) source.1 -
    inner ℂ (annularEnergyD lower length positive test) source.2.1 -
    inner ℂ (annularEnergyCell lower length positive test) source.2.2.1 -
    inner ℂ (annularEnergyTrace lower length positive bounded lengthPositive 1 test) source.2.2.2

def annularTiltFunctional (source : AnnularForcing lower) : annularEnergySpace lower length positive →L[ℝ] ℝ :=
  (innerSL ℝ source.1).comp
      ((annularTiltSourceTest parameters lower length positive lengthPositive widthHalf widthLength).restrictScalars ℝ) -
    (innerSL ℝ source.2.1).comp ((annularEnergyD lower length positive).restrictScalars ℝ) -
    (innerSL ℝ source.2.2.1).comp ((annularEnergyCell lower length positive).restrictScalars ℝ) -
    (innerSL ℝ source.2.2.2).comp ((annularEnergyTrace lower length positive bounded lengthPositive 1).restrictScalars ℝ)

theorem annularTiltFunctional_literal (source : AnnularForcing lower) (test : annularEnergySpace lower length positive) :
    annularTiltFunctional parameters lower length positive bounded lengthPositive widthHalf widthLength source test =
      (annularTiltFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source test).re := by
  change (inner ℂ source.1 (annularTiltSourceTest parameters lower length positive lengthPositive widthHalf widthLength test)).re -
    (inner ℂ source.2.1 (annularEnergyD lower length positive test)).re -
    (inner ℂ source.2.2.1 (annularEnergyCell lower length positive test)).re -
    (inner ℂ source.2.2.2 (annularEnergyTrace lower length positive bounded lengthPositive 1 test)).re = _
  simp only [annularTiltFunctionalValue, Complex.sub_re]
  exact congrArg₂ (fun first second : ℝ => first - second)
    (congrArg₂ (fun first second : ℝ => first - second)
      (congrArg₂ (fun first second : ℝ => first - second)
        (inner_re_symm (𝕜 := ℂ) _ _) (inner_re_symm (𝕜 := ℂ) _ _))
      (inner_re_symm (𝕜 := ℂ) _ _)) (inner_re_symm (𝕜 := ℂ) _ _)

theorem annularTiltFunctionalValue_test_smul (source : AnnularForcing lower)
    (test : annularEnergySpace lower length positive) (scalar : ℂ) :
    annularTiltFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source (scalar • test) =
      (starRingEnd ℂ scalar) *
        annularTiltFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source test := by
  simp only [annularTiltFunctionalValue, map_smul, inner_smul_left]
  ring

theorem annularTiltFunctionalValue_bound (source : AnnularForcing lower) (test : annularEnergySpace lower length positive) :
    ‖annularTiltFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source test‖ ≤
      annularForcingSize lower length source * ‖test‖ := by
  have first := (norm_inner_le_norm (𝕜 := ℂ)
    (annularTiltSourceTest parameters lower length positive lengthPositive widthHalf widthLength test) source.1).trans
      (mul_le_mul_of_nonneg_right (annularTiltSourceTest_bound parameters lower length positive lengthPositive widthHalf widthLength test)
        (norm_nonneg source.1))
  have second := (norm_inner_le_norm (𝕜 := ℂ) (annularEnergyD lower length positive test) source.2.1).trans
    (mul_le_mul_of_nonneg_right (annularEnergyD_bound lower length positive test) (norm_nonneg source.2.1))
  have third := (norm_inner_le_norm (𝕜 := ℂ) (annularEnergyCell lower length positive test) source.2.2.1).trans
    (mul_le_mul_of_nonneg_right (annularEnergyCell_bound lower length positive test) (norm_nonneg source.2.2.1))
  have fourth := (norm_inner_le_norm (𝕜 := ℂ) (annularEnergyTrace lower length positive bounded lengthPositive 1 test) source.2.2.2).trans
    (mul_le_mul_of_nonneg_right (annularEnergyTrace_bound lower length positive bounded lengthPositive 1 test) (norm_nonneg source.2.2.2))
  have triangle := (norm_sub_le
    (inner ℂ (annularTiltSourceTest parameters lower length positive lengthPositive widthHalf widthLength test) source.1 -
      inner ℂ (annularEnergyD lower length positive test) source.2.1 -
      inner ℂ (annularEnergyCell lower length positive test) source.2.2.1)
    (inner ℂ (annularEnergyTrace lower length positive bounded lengthPositive 1 test) source.2.2.2)).trans
      (add_le_add ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
  unfold annularTiltFunctionalValue annularForcingSize
  nlinarith only [triangle, first, second, third, fourth]

end Functional

end Grad.AnnularTiltedReference
