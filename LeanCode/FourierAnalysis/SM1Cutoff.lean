import COR16Consumer
import P0910Plateau
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section

open Set
open scoped ContDiff Topology

namespace Grad.SmoothingFamily

open Grad.DiskExtension.Operator

/-- The fixed accepted P1 plateau cutoff, rescaled to the literal intervals
(-infinity,1] and [2,infinity) used in P18. -/
def eta (scale : ℝ) : ℝ := plateauCutoff (scale / 12)

theorem eta_smooth : ContDiff ℝ ∞ eta :=
  plateauCutoff_smooth.comp (contDiff_id.div_const 12)

theorem eta_range (scale : ℝ) : 0 ≤ eta scale ∧ eta scale ≤ 1 :=
  plateauCutoff_range _

theorem eta_one (scale : ℝ) (bound : scale ≤ 1) : eta scale = 1 := by
  apply plateauCutoff_one
  rw [collar_constants.2.1]
  linarith

theorem eta_zero (scale : ℝ) (bound : 2 ≤ scale) : eta scale = 0 := by
  apply plateauCutoff_zero
  rw [collar_constants.2.2.1]
  linarith

/-- The actual P20 recurrence for the scale derivative profiles. -/
def scaleProfile (order : ℕ) : ℝ → ℝ :=
  Nat.rec eta (fun previous profile scale =>
    -(previous : ℝ) * profile scale - scale * deriv profile scale) order

theorem scaleProfile_zero : scaleProfile 0 = eta := rfl

theorem scaleProfile_succ (order : ℕ) (scale : ℝ) :
    scaleProfile (order + 1) scale = -(order : ℝ) * scaleProfile order scale -
      scale * deriv (scaleProfile order) scale := rfl

theorem scaleProfile_smooth (order : ℕ) : ContDiff ℝ ∞ (scaleProfile order) := by
  induction order with
  | zero => exact eta_smooth
  | succ order inductionHypothesis =>
    exact (contDiff_const.mul inductionHypothesis).sub
      (contDiff_id.mul inductionHypothesis.deriv')

theorem scaleProfile_left (order : ℕ) (scale : ℝ) (bound : scale < 1) :
    scaleProfile order scale = if order = 0 then 1 else 0 := by
  induction order generalizing scale with
  | zero => simpa only [scaleProfile_zero, ↓reduceIte] using eta_one scale bound.le
  | succ order inductionHypothesis =>
    have localConstant : EqOn (scaleProfile order)
        (fun _ : ℝ => if order = 0 then 1 else 0) (Iio 1) := by
      intro point member
      exact inductionHypothesis point member
    have derivativeZero : deriv (scaleProfile order) scale = 0 := by
      simpa only [iteratedDeriv_one, deriv_const] using
        localConstant.iteratedDeriv_of_isOpen isOpen_Iio 1 bound
    rw [scaleProfile_succ, derivativeZero, mul_zero, sub_zero, inductionHypothesis scale bound]
    by_cases zeroOrder : order = 0
    · simp [zeroOrder]
    · simp [zeroOrder]

theorem scaleProfile_right (order : ℕ) (scale : ℝ) (bound : 2 < scale) :
    scaleProfile order scale = 0 := by
  induction order generalizing scale with
  | zero => exact eta_zero scale bound.le
  | succ order inductionHypothesis =>
    have localConstant : EqOn (scaleProfile order) (fun _ : ℝ => 0) (Ioi 2) := by
      intro point member
      exact inductionHypothesis point member
    have derivativeZero : deriv (scaleProfile order) scale = 0 := by
      simpa only [iteratedDeriv_one, deriv_const] using
        localConstant.iteratedDeriv_of_isOpen isOpen_Ioi 1 bound
    rw [scaleProfile_succ, inductionHypothesis scale bound, derivativeZero]
    ring

theorem scaleProfile_compact (order : ℕ) (positive : 0 < order) :
    HasCompactSupport (scaleProfile order) := by
  rw [HasCompactSupport]
  apply (isCompact_Icc : IsCompact (Icc (1 : ℝ) 2)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro scale nonzero
  by_contra outside
  simp only [mem_Icc, not_and_or, not_le] at outside
  rcases outside with left | right
  · exact nonzero (by rw [scaleProfile_left order scale left, if_neg positive.ne'])
  · exact nonzero (scaleProfile_right order scale right)

theorem scaleProfile_bounded (order : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ scale, ‖scaleProfile order scale‖ ≤ bound := by
  by_cases zeroOrder : order = 0
  · subst order
    refine ⟨1, zero_le_one, fun scale => ?_⟩
    rw [scaleProfile_zero, Real.norm_eq_abs, abs_of_nonneg (eta_range scale).1]
    exact (eta_range scale).2
  · obtain ⟨bound, bound_all⟩ := (scaleProfile_smooth order).continuous.bounded_above_of_compact_support
      (scaleProfile_compact order (Nat.pos_of_ne_zero zeroOrder))
    exact ⟨max bound 0, le_max_right _ _, fun scale => (bound_all scale).trans (le_max_left _ _)⟩

end Grad.SmoothingFamily
