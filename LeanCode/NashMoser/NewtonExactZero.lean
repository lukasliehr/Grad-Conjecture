import NewtonGradeLimits

noncomputable section

open Filter
open scoped Topology

namespace Grad.NashMoser.Numeric

theorem newtonTime_decay_tendsto {initial exponent : ℝ}
    (initialLarge : 4 ≤ initial) (exponentLarge : 2 ≤ exponent) :
    Tendsto (fun index : ℕ => newtonTime initial index ^ (-exponent)) atTop (𝓝 0) := by
  let ratio := initial ^ (-exponent / 2)
  have positive : 0 < initial := by linarith
  have ratioNonnegative : 0 ≤ ratio := Real.rpow_nonneg positive.le _
  have ratioBound : ratio ≤ 1 / 2 := by
    simpa only [newtonTime, pow_zero, Real.rpow_one] using
      newtonTime_ratio_le initialLarge exponentLarge 0
  have geometric := (tendsto_pow_atTop_nhds_zero_of_lt_one ratioNonnegative
    (by linarith : ratio < 1)).const_mul (initial ^ (-exponent))
  have majorant : ∀ index : ℕ,
      newtonTime initial index ^ (-exponent) ≤ initial ^ (-exponent) * ratio ^ index := by
    intro index
    simpa only [zero_add, newtonTime, pow_zero, Real.rpow_one] using
      newtonTime_geometric_majorant initialLarge exponentLarge 0 index
  apply squeeze_zero (fun index => Real.rpow_nonneg
    (newtonTime_pos positive index).le _) majorant
  simpa only [mul_zero] using geometric

namespace GuardedNewtonData

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  {initial radius highConstant quadratic : ℝ} {smoothing : ℕ → ℝ} {loss : ℕ}
  (data : GuardedNewtonData E F initial radius highConstant quadratic smoothing loss)

theorem iterate_residual_tendsto_zero :
    Tendsto (fun index => data.mapping (data.iterate index)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have exponentLarge : 2 ≤ initialDecay (loss : ℝ) := by
    unfold initialDecay
    nlinarith [Nat.cast_nonneg (α := ℝ) loss]
  exact squeeze_zero (fun _ => norm_nonneg _) data.iterate_residual_decay
    (newtonTime_decay_tendsto data.initialLarge exponentLarge)

/-- Equality, not a weak or projected zero: normed-target uniqueness closes
the equation once the constructed iterates converge at a continuity grade. -/
theorem exact_zero_of_grade_limit
    {G : Type*} [NormedAddCommGroup G]
    (gradeMap : E →+ G) (candidate : E)
    (completedMapping : G → F)
    (realization : ∀ state, completedMapping (gradeMap state) = data.mapping state)
    (mappingContinuous : ContinuousAt completedMapping (gradeMap candidate))
    (convergence : Tendsto (fun index => gradeMap (data.iterate index)) atTop
      (𝓝 (gradeMap candidate))) :
    data.mapping candidate = 0 := by
  have mapped := mappingContinuous.tendsto.comp convergence
  simp only [Function.comp_def, realization] at mapped
  exact tendsto_nhds_unique mapped data.iterate_residual_tendsto_zero

end GuardedNewtonData

end Grad.NashMoser.Numeric
