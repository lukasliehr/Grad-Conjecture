import SM2ScaleDerivatives

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace Grad.SmoothingFamily

open Grad.FourierGrade

theorem frequency_sublevel_finite (bound : ℝ) :
    Set.Finite {mode : FourierMode | frequencyWeight mode ≤ bound} := by
  let upper := max bound 1
  have upperPositive : 0 < upper := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have thresholdPositive : 0 < (upper ^ 6)⁻¹ := inv_pos.mpr (pow_pos upperPositive 6)
  have small : ∀ᶠ mode in Filter.cofinite, inverseSixWeight mode < (upper ^ 6)⁻¹ :=
    inverseSixWeight_summable.tendsto_cofinite_zero.eventually (gt_mem_nhds thresholdPositive)
  apply (Filter.eventually_cofinite.mp small).subset
  intro mode below
  apply not_lt_of_ge
  exact (inv_le_inv₀ (pow_pos upperPositive 6) (pow_pos (frequencyWeight_pos mode) 6)).mpr
    (pow_le_pow_left₀ (frequencyWeight_pos mode).le (below.trans (le_max_left _ _)) 6)

/-- A real bounded diagonal multiplier on the actual all-grade Fourier core. -/
def boundedCoreMultiplier {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (factor : FourierMode → ℝ) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (factorBound : ∀ mode, ‖factor mode‖ ≤ bound) : JCore Value →ₗ[ℂ] JCore Value where
  toFun values := ⟨fun mode => (factor mode : ℂ) • values.1 mode, by
    intro grade
    apply Memℓp.mono' ((values.property grade).const_smul (bound : ℂ))
    intro mode
    change ‖(frequencyWeight mode : ℂ) ^ grade • ((factor mode : ℂ) • values.1 mode)‖ ≤
      ‖(bound : ℂ) • ((frequencyWeight mode : ℂ) ^ grade • values.1 mode)‖
    rw [smul_comm ((frequencyWeight mode : ℂ) ^ grade) (factor mode : ℂ)]
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg boundNonnegative]
    exact mul_le_mul_of_nonneg_right (factorBound mode) (mul_nonneg (norm_nonneg _) (norm_nonneg _))⟩
  map_add' first second := by
    apply Subtype.ext
    funext mode
    exact smul_add (factor mode : ℂ) (first.1 mode) (second.1 mode)
  map_smul' scalar values := by
    apply Subtype.ext
    funext mode
    exact smul_comm (factor mode : ℂ) scalar (values.1 mode)

theorem boundedCoreMultiplier_apply {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (factor : FourierMode → ℝ) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (factorBound : ∀ mode, ‖factor mode‖ ≤ bound) (values : JCore Value) (mode : FourierMode) :
    (boundedCoreMultiplier factor bound boundNonnegative factorBound values).1 mode =
      (factor mode : ℂ) • values.1 mode := rfl

theorem core_weighted_norm {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (values : JCore Value) (grade : ℕ) (mode : FourierMode) :
    ‖coreToGrade grade values mode‖ = frequencyWeight mode ^ grade * ‖values.1 mode‖ := by
  change ‖(frequencyWeight mode : ℂ) ^ grade • values.1 mode‖ = _
  rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (frequencyWeight_pos mode)]

/-- A coefficientwise weighted norm comparison yields the literal grade bound. -/
theorem core_norm_le_of_weighted_bound {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (first second : JCore Value) (firstGrade secondGrade : ℕ) (bound : ℝ)
    (boundNonnegative : 0 ≤ bound)
    (pointwise : ∀ mode, frequencyWeight mode ^ firstGrade * ‖first.1 mode‖ ≤
      bound * (frequencyWeight mode ^ secondGrade * ‖second.1 mode‖)) :
    ‖coreToGrade firstGrade first‖ ≤ bound * ‖coreToGrade secondGrade second‖ := by
  have comparison := lp.norm_mono (p := 2) (by norm_num)
    (x := coreToGrade firstGrade first) (y := (bound : ℂ) • coreToGrade secondGrade second) (by
      intro mode
      rw [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg boundNonnegative, core_weighted_norm, core_weighted_norm]
      exact pointwise mode)
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg boundNonnegative]
    using comparison

/-- Literal P18 on the common coefficient core, chosen independently of grade. -/
def fourierSmoothing {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (scale : ℝ) : JCore Value →ₗ[ℂ] JCore Value :=
  boundedCoreMultiplier (fun mode => eta (frequencyWeight mode / scale)) 1 zero_le_one
    (fun mode => by rw [Real.norm_eq_abs, abs_of_nonneg (eta_range _).1]; exact (eta_range _).2)

theorem fourierSmoothing_apply {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (scale : ℝ) (values : JCore Value) (mode : FourierMode) :
    (fourierSmoothing scale values).1 mode =
      (eta (frequencyWeight mode / scale) : ℂ) • values.1 mode := rfl

theorem fourierSmoothing_finite_support {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (scale : ℝ) (positive : 0 < scale) (values : JCore Value) :
    Set.Finite (Function.support (fourierSmoothing scale values).1) := by
  apply (frequency_sublevel_finite (2 * scale)).subset
  intro mode nonzero
  by_contra outside
  have cutoffZero : eta (frequencyWeight mode / scale) = 0 :=
    eta_zero _ ((le_div_iff₀ positive).mpr (le_of_lt (lt_of_not_ge outside)))
  apply nonzero
  rw [fourierSmoothing_apply, cutoffZero, Complex.ofReal_zero, zero_smul]

end Grad.SmoothingFamily
