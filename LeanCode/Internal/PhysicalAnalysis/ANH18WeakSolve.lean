import ANH17RobinForm
import ANH15EnergyGraph

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.CircularHighWeak
open Grad.CartesianState

private theorem realCoercive_solution {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (form : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive form)
    (source : V →L[ℝ] ℝ) (test : V) :
    form (coercive.continuousLinearEquivOfBilin.symm
      ((InnerProductSpace.toDual ℝ V).symm source)) test = source test := by
  have equality := coercive.continuousLinearEquivOfBilin_apply
    (coercive.continuousLinearEquivOfBilin.symm ((InnerProductSpace.toDual ℝ V).symm source)) test
  rw [ContinuousLinearEquiv.apply_symm_apply, InnerProductSpace.toDual_symm_apply] at equality
  exact equality.symm
private theorem realCoercive_separates {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (form : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive form)
    (first second : V) (equal : ∀ test, form first test = form second test) : first = second := by
  apply coercive.continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro test
  rw [IsCoercive.continuousLinearEquivOfBilin_apply, IsCoercive.continuousLinearEquivOfBilin_apply]
  exact equal test

private theorem imaginary_part (value : ℂ) :
    (starRingEnd ℂ Complex.I * value).re = value.im := by simp

private def robinRHS (source : highDiskL2) : highDiskGrade →L[ℝ] ℝ :=
  (innerSL ℝ source.val).comp (highDiskBulk.restrictScalars ℝ)

/-- The weak solution is constructed by the Hilbert inverse of the proved
coercive form, applied to the actual high L2 source functional. -/
def weakSolution (parameter : ℝ) (source : highDiskL2) : highDiskGrade :=
  (robinForm_isCoercive parameter).continuousLinearEquivOfBilin.symm
    ((InnerProductSpace.toDual ℝ highDiskGrade).symm (robinRHS source))

theorem weakSolution_real (parameter : ℝ) (source : highDiskL2) (test : highDiskGrade) :
    robinForm parameter (weakSolution parameter source) test = inner ℝ source.val (highDiskBulk test) := by
  exact realCoercive_solution (robinForm parameter) (robinForm_isCoercive parameter) (robinRHS source) test

private theorem robinValue_smul_test (parameter : ℝ) (scalar : ℂ) (field test : highDiskGrade) :
    robinValue parameter field (scalar • test) = starRingEnd ℂ scalar * robinValue parameter field test := by
  simp only [robinValue, map_smul, inner_smul_left]
  ring

private theorem robinValue_smul_field (parameter : ℝ) (scalar : ℂ) (field test : highDiskGrade) :
    robinValue parameter (scalar • field) test = scalar * robinValue parameter field test := by
  simp only [robinValue, map_smul, inner_smul_right]
  ring

private theorem robinValue_add_field (parameter : ℝ) (first second test : highDiskGrade) :
    robinValue parameter (first + second) test =
      robinValue parameter first test + robinValue parameter second test := by
  simp only [robinValue, map_add, inner_add_right]
  ring

/-- The literal AN18 complex equation, for every test in the actual high
full-disk H1 completion. No PDE inverse is assumed. -/
theorem weakSolution_equation (parameter : ℝ) (source : highDiskL2) (test : highDiskGrade) :
    robinValue parameter (weakSolution parameter source) test = inner ℂ (highDiskBulk test) source.val := by
  have realPart (probe : highDiskGrade) :
      (robinValue parameter (weakSolution parameter source) probe).re =
        (inner ℂ (highDiskBulk probe) source.val).re :=
    (robinForm_literal parameter (weakSolution parameter source) probe).symm.trans
      ((weakSolution_real parameter source probe).trans (inner_re_symm (𝕜 := ℂ) _ _))
  have leftImaginary :
      (robinValue parameter (weakSolution parameter source) (Complex.I • test)).re =
        (robinValue parameter (weakSolution parameter source) test).im :=
    (congrArg Complex.re (robinValue_smul_test parameter Complex.I (weakSolution parameter source) test)).trans
      (imaginary_part _)
  have rightPairing : inner ℂ (highDiskBulk (Complex.I • test)) source.val =
      starRingEnd ℂ Complex.I * inner ℂ (highDiskBulk test) source.val :=
    (congrArg (fun value : DiskL2 1 => inner ℂ value source.val)
      (highDiskBulk.map_smul Complex.I test)).trans (inner_smul_left _ _ _)
  have rightImaginary : (inner ℂ (highDiskBulk (Complex.I • test)) source.val).re =
      (inner ℂ (highDiskBulk test) source.val).im :=
    (congrArg Complex.re rightPairing).trans (imaginary_part _)
  exact Complex.ext (realPart test)
    (leftImaginary.symm.trans ((realPart (Complex.I • test)).trans rightImaginary))

private theorem robinForm_separates (parameter : ℝ) (first second : highDiskGrade)
    (equal : ∀ test, robinForm parameter first test = robinForm parameter second test) : first = second := by
  exact realCoercive_separates (robinForm parameter) (robinForm_isCoercive parameter) first second equal

/-- Uniqueness has no regularity assumption beyond membership of the high
energy completion. -/
theorem weakSolution_unique (parameter : ℝ) (source : highDiskL2) (field : highDiskGrade)
    (equation : ∀ test, robinValue parameter field test = inner ℂ (highDiskBulk test) source.val) :
    field = weakSolution parameter source := by
  apply robinForm_separates parameter
  intro test
  exact (robinForm_literal parameter field test).trans
    ((congrArg Complex.re ((equation test).trans (weakSolution_equation parameter source test).symm)).trans
      (robinForm_literal parameter (weakSolution parameter source) test).symm)

/-- The AN18 H1 estimate is uniform for every real parameter. -/
theorem weakSolution_bound (parameter : ℝ) (source : highDiskL2) :
    ‖weakSolution parameter source‖ ≤ 2 * ‖source‖ := by
  have coercive := (robinForm_coercivity parameter (weakSolution parameter source)).trans_eq
    (weakSolution_real parameter source (weakSolution parameter source))
  have cauchy := real_inner_le_norm source.val (highDiskBulk (weakSolution parameter source))
  have bulk := mul_le_mul_of_nonneg_left (highBulk_norm_le (weakSolution parameter source)) (norm_nonneg source.val)
  have bound := coercive.trans (cauchy.trans bulk)
  change (1 / 2 : ℝ) * ‖weakSolution parameter source‖ ^ 2 ≤ ‖source‖ * ‖weakSolution parameter source‖ at bound
  nlinarith only [bound, norm_nonneg (weakSolution parameter source), norm_nonneg source]

private theorem weakSolution_add (parameter : ℝ) (first second : highDiskL2) :
    weakSolution parameter (first + second) = weakSolution parameter first + weakSolution parameter second := by
  symm
  apply weakSolution_unique parameter (first + second)
  intro test
  exact (robinValue_add_field parameter (weakSolution parameter first) (weakSolution parameter second) test).trans
    ((congrArg₂ (fun first second : ℂ => first + second)
      (weakSolution_equation parameter first test) (weakSolution_equation parameter second test)).trans
      (inner_add_right _ _ _).symm)

private theorem weakSolution_smul (parameter : ℝ) (scalar : ℂ) (source : highDiskL2) :
    weakSolution parameter (scalar • source) = scalar • weakSolution parameter source := by
  symm
  apply weakSolution_unique parameter (scalar • source)
  intro test
  exact (robinValue_smul_field parameter scalar (weakSolution parameter source) test).trans
    ((congrArg (fun value : ℂ => scalar * value) (weakSolution_equation parameter source test)).trans
      (inner_smul_right _ _ _).symm)

/-- The actual AN18 high L2 to high H1 weak inverse, at the same disk and
parameter, with its bounded complex linear structure proved from uniqueness. -/
def highRobinWeakInverse (parameter : ℝ) : highDiskL2 →L[ℂ] highDiskGrade :=
  ({ toFun := weakSolution parameter
     map_add' := weakSolution_add parameter
     map_smul' := weakSolution_smul parameter } : highDiskL2 →ₗ[ℂ] highDiskGrade).mkContinuous 2
    (weakSolution_bound parameter)

theorem highRobinWeakInverse_equation (parameter : ℝ) (source : highDiskL2) (test : highDiskGrade) :
    robinValue parameter (highRobinWeakInverse parameter source) test = inner ℂ (highDiskBulk test) source.val :=
  weakSolution_equation parameter source test

theorem highRobinWeakInverse_uniform (parameter : ℝ) : ‖highRobinWeakInverse parameter‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (weakSolution_bound parameter)

end Grad.CircularHighWeak
