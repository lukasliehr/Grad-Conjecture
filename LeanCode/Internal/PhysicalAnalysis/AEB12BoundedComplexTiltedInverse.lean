import AEB11TiltedReferenceUniquenessBound

noncomputable section
set_option maxHeartbeats 1000000

namespace Grad.AnnularTiltedReference

open Grad.CartesianState Grad.AnnularVariational

section Inverse
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem annularTiltFunctionalValue_source_add (first second : AnnularForcing lower)
    (test : annularEnergySpace lower length positive) :
    annularTiltFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength (first + second) test =
      annularTiltFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength first test +
        annularTiltFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength second test := by
  simp only [annularTiltFunctionalValue, Prod.fst_add, Prod.snd_add, inner_add_right]
  ring

theorem annularTiltFunctionalValue_source_smul (source : AnnularForcing lower)
    (test : annularEnergySpace lower length positive) (scalar : ℂ) :
    annularTiltFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength (scalar • source) test =
      scalar * annularTiltFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source test := by
  simp only [annularTiltFunctionalValue, Prod.smul_fst, Prod.smul_snd, inner_smul_right]
  ring

theorem annularTiltVariationalSolution_add (first second : AnnularForcing lower) (firstInner secondInner : AnnularBoundary) :
    annularTiltVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength (first + second) (firstInner + secondInner) =
      annularTiltVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength first firstInner +
        annularTiltVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength second secondInner := by
  symm
  apply annularTiltVariationalSolution_unique parameters lower length positive bounded lengthPositive widthHalf widthLength
  · rw [map_add, annularTiltVariationalSolution_inner, annularTiltVariationalSolution_inner]
  · intro test
    rw [annularTiltFormValue_field_add, annularTiltVariationalSolution_weak, annularTiltVariationalSolution_weak,
      annularTiltFunctionalValue_source_add]

theorem annularTiltVariationalSolution_smul (source : AnnularForcing lower) (innerValue : AnnularBoundary) (scalar : ℂ) :
    annularTiltVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength (scalar • source) (scalar • innerValue) =
      scalar • annularTiltVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue := by
  symm
  apply annularTiltVariationalSolution_unique parameters lower length positive bounded lengthPositive widthHalf widthLength
  · rw [map_smul, annularTiltVariationalSolution_inner]
  · intro test
    rw [annularTiltFormValue_field_smul, annularTiltVariationalSolution_weak, annularTiltFunctionalValue_source_smul]

/-- The complex-linear inverse on the independently prescribed bulk, outer,
and inner data. The present bound is for each fixed collar; the coercive dual inverse bound is uniform. -/
def annularTiltVariationalLinear : (AnnularForcing lower × AnnularBoundary) →ₗ[ℂ] annularEnergySpace lower length positive where
  toFun := fun data => annularTiltVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2
  map_add' := fun first second => annularTiltVariationalSolution_add parameters lower length positive bounded lengthPositive widthHalf widthLength first.1 second.1 first.2 second.2
  map_smul' := fun scalar data => annularTiltVariationalSolution_smul parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 scalar

def annularTiltInverseConstant (lower length : ℝ) : ℝ :=
  (16 : ℝ) * (5 + annularTraceConstant lower length) + (65 : ℝ) * annularInnerLiftConstant lower length

theorem annularTiltVariationalLinear_bound (data : AnnularForcing lower × AnnularBoundary) :
    ‖annularTiltVariationalLinear parameters lower length positive bounded lengthPositive widthHalf widthLength data‖ ≤
      annularTiltInverseConstant lower length * ‖data‖ := by
  have energy := annularTiltVariationalSolution_bound parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2
  have sourceBound := (annularForcingSize_bound lower length data.1).trans
    (mul_le_mul_of_nonneg_left (norm_fst_le data) (by
      have h : 0 ≤ annularTraceConstant lower length := Real.sqrt_nonneg _
      linarith only [h]))
  have innerBound := mul_le_mul_of_nonneg_left (norm_snd_le data)
    (show 0 ≤ annularInnerLiftConstant lower length from Real.sqrt_nonneg _)
  change ‖annularTiltVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2‖ ≤ _
  unfold annularTiltInverseConstant
  nlinarith only [energy, sourceBound, innerBound]

def annularTiltVariationalInverse : (AnnularForcing lower × AnnularBoundary) →L[ℂ] annularEnergySpace lower length positive :=
  (annularTiltVariationalLinear parameters lower length positive bounded lengthPositive widthHalf widthLength).mkContinuous
    (annularTiltInverseConstant lower length)
    (annularTiltVariationalLinear_bound parameters lower length positive bounded lengthPositive widthHalf widthLength)

end Inverse

end Grad.AnnularTiltedReference
