import SM1Cutoff

noncomputable section

open Set
open scoped ContDiff Topology

namespace Grad.SmoothingFamily

/-- The actual scalar scale derivative multiplier of order `j`. -/
def scaleMultiplier (order : ℕ) (frequency scale : ℝ) : ℝ :=
  scale ^ (-(order : ℝ)) * scaleProfile order (frequency / scale)

theorem scaleMultiplier_zero (frequency scale : ℝ) :
    scaleMultiplier 0 frequency scale = eta (frequency / scale) := by
  simp only [scaleMultiplier, Nat.cast_zero, neg_zero, Real.rpow_zero, one_mul, scaleProfile_zero]

theorem scaleMultiplier_hasDerivAt (order : ℕ) (frequency scale : ℝ) (positive : 0 < scale) :
    HasDerivAt (scaleMultiplier order frequency) (scaleMultiplier (order + 1) frequency scale) scale := by
  have nonzero : scale ≠ 0 := positive.ne'
  have powerDerivative := Real.hasDerivAt_rpow_const
    (x := scale) (p := -(order : ℝ)) (Or.inl nonzero)
  have quotientDerivative := (hasDerivAt_const scale frequency).div (hasDerivAt_id scale) nonzero
  have profileDerivative := (((scaleProfile_smooth order).differentiable (by simp)).differentiableAt
    (x := frequency / scale)).hasDerivAt
  have composed := profileDerivative.comp scale quotientDerivative
  have multiplied := powerDerivative.mul composed
  have powerIdentity : scale ^ (-(order : ℝ)) = scale ^ (-(order : ℝ) - 1) * scale := by
    calc
      _ = scale ^ ((-(order : ℝ) - 1) + 1) := by congr 1; ring
      _ = scale ^ (-(order : ℝ) - 1) * scale ^ (1 : ℝ) := Real.rpow_add positive _ _
      _ = _ := by rw [Real.rpow_one]
  apply multiplied.congr_deriv
  unfold scaleMultiplier
  rw [scaleProfile_succ]
  have exponentIdentity : -((order + 1 : ℕ) : ℝ) = -(order : ℝ) - 1 := by push_cast; ring
  rw [exponentIdentity, powerIdentity]
  simp only [Function.comp_apply, id_eq]
  field_simp [nonzero]
  ring

/-- The recurrence gives genuine iterated scale derivatives on `T>0`. -/
theorem iteratedDeriv_eta_scaled (order : ℕ) (frequency scale : ℝ) (positive : 0 < scale) :
    iteratedDeriv order (fun parameter : ℝ => eta (frequency / parameter)) scale =
      scaleMultiplier order frequency scale := by
  induction order generalizing scale with
  | zero => exact (scaleMultiplier_zero frequency scale).symm
  | succ order inductionHypothesis =>
    rw [iteratedDeriv_succ]
    have locallyEqual : iteratedDeriv order (fun parameter : ℝ => eta (frequency / parameter))
        =ᶠ[nhds scale] scaleMultiplier order frequency := by
      filter_upwards [isOpen_Ioi.mem_nhds positive] with parameter parameterPositive
      exact inductionHypothesis parameter parameterPositive
    rw [locallyEqual.deriv_eq]
    exact (scaleMultiplier_hasDerivAt order frequency scale positive).deriv

theorem scaleMultiplier_support (order : ℕ) (positiveOrder : 0 < order)
    (frequency scale : ℝ) (positiveScale : 0 < scale)
    (nonzero : scaleMultiplier order frequency scale ≠ 0) :
    scale ≤ frequency ∧ frequency ≤ 2 * scale := by
  have profileNonzero : scaleProfile order (frequency / scale) ≠ 0 := by
    intro equality
    apply nonzero
    rw [scaleMultiplier, equality, mul_zero]
  constructor
  · by_contra notLower
    have ratio : frequency / scale < 1 := (div_lt_one positiveScale).mpr (lt_of_not_ge notLower)
    exact profileNonzero (by rw [scaleProfile_left order _ ratio, if_neg positiveOrder.ne'])
  · by_contra notUpper
    have ratio : 2 < frequency / scale := (lt_div_iff₀ positiveScale).mpr (lt_of_not_ge notUpper)
    exact profileNonzero (scaleProfile_right order _ ratio)

end Grad.SmoothingFamily
