import AAG18UniqueInverseBound
import AAG19InnerZeroDensity

noncomputable section
set_option maxHeartbeats 1000000

namespace Grad.AnnularVariational

open Grad.CartesianState

section Inverse
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem annularFunctionalValue_source_add (first second : AnnularForcing lower)
    (test : annularEnergySpace lower length positive) :
    annularFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength (first + second) test =
      annularFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength first test +
        annularFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength second test := by
  simp only [annularFunctionalValue, Prod.fst_add, Prod.snd_add, inner_add_right]
  ring

theorem annularFunctionalValue_source_smul (source : AnnularForcing lower)
    (test : annularEnergySpace lower length positive) (scalar : ℂ) :
    annularFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength (scalar • source) test =
      scalar * annularFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source test := by
  simp only [annularFunctionalValue, Prod.smul_fst, Prod.smul_snd, inner_smul_right]
  ring

theorem annularVariationalSolution_add (first second : AnnularForcing lower) (firstInner secondInner : AnnularBoundary) :
    annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength (first + second) (firstInner + secondInner) =
      annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength first firstInner +
        annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength second secondInner := by
  symm
  apply annularVariationalSolution_unique parameters lower length positive bounded lengthPositive widthHalf widthLength
  · rw [map_add, annularVariationalSolution_inner, annularVariationalSolution_inner]
  · intro test
    rw [annularFormValue_field_add, annularVariationalSolution_weak, annularVariationalSolution_weak,
      annularFunctionalValue_source_add]

theorem annularVariationalSolution_smul (source : AnnularForcing lower) (innerValue : AnnularBoundary) (scalar : ℂ) :
    annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength (scalar • source) (scalar • innerValue) =
      scalar • annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue := by
  symm
  apply annularVariationalSolution_unique parameters lower length positive bounded lengthPositive widthHalf widthLength
  · rw [map_smul, annularVariationalSolution_inner]
  · intro test
    rw [annularFormValue_field_smul, annularVariationalSolution_weak, annularFunctionalValue_source_smul]

/-- The complex-linear inverse on the independently prescribed bulk, outer,
and inner data. Its stronger physical sum estimate is AG20. -/
def annularVariationalLinear : (AnnularForcing lower × AnnularBoundary) →ₗ[ℂ] annularEnergySpace lower length positive where
  toFun := fun data => annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2
  map_add' := fun first second => annularVariationalSolution_add parameters lower length positive bounded lengthPositive widthHalf widthLength first.1 second.1 first.2 second.2
  map_smul' := fun scalar data => annularVariationalSolution_smul parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 scalar

theorem annularForcingSize_bound (source : AnnularForcing lower) :
    annularForcingSize lower length source ≤ (5 + annularTraceConstant lower length) * ‖source‖ := by
  have first : ‖source.1‖ ≤ ‖source‖ := norm_fst_le source
  have second : ‖source.2.1‖ ≤ ‖source‖ := (norm_fst_le source.2).trans (norm_snd_le source)
  have third : ‖source.2.2.1‖ ≤ ‖source‖ := (norm_fst_le source.2.2).trans ((norm_snd_le source.2).trans (norm_snd_le source))
  have fourth : ‖source.2.2.2‖ ≤ ‖source‖ := (norm_snd_le source.2.2).trans ((norm_snd_le source.2).trans (norm_snd_le source))
  have traceNonnegative : 0 ≤ annularTraceConstant lower length := Real.sqrt_nonneg _
  have traceBound := mul_le_mul_of_nonneg_left fourth traceNonnegative
  unfold annularForcingSize
  nlinarith only [first, second, third, traceBound]

def annularInverseConstant (lower length : ℝ) : ℝ :=
  (4 / 3 : ℝ) * (5 + annularTraceConstant lower length) + (19 / 3 : ℝ) * annularInnerLiftConstant lower length

theorem annularVariationalLinear_bound (data : AnnularForcing lower × AnnularBoundary) :
    ‖annularVariationalLinear parameters lower length positive bounded lengthPositive widthHalf widthLength data‖ ≤
      annularInverseConstant lower length * ‖data‖ := by
  have energy := annularVariationalSolution_bound parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2
  have sourceBound := (annularForcingSize_bound lower length data.1).trans
    (mul_le_mul_of_nonneg_left (norm_fst_le data) (by
      have h : 0 ≤ annularTraceConstant lower length := Real.sqrt_nonneg _
      linarith only [h]))
  have innerBound := mul_le_mul_of_nonneg_left (norm_snd_le data)
    (show 0 ≤ annularInnerLiftConstant lower length from Real.sqrt_nonneg _)
  change ‖annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2‖ ≤ _
  unfold annularInverseConstant
  nlinarith only [energy, sourceBound, innerBound]

def annularVariationalInverse : (AnnularForcing lower × AnnularBoundary) →L[ℂ] annularEnergySpace lower length positive :=
  (annularVariationalLinear parameters lower length positive bounded lengthPositive widthHalf widthLength).mkContinuous
    (annularInverseConstant lower length)
    (annularVariationalLinear_bound parameters lower length positive bounded lengthPositive widthHalf widthLength)

end Inverse

end Grad.AnnularVariational
