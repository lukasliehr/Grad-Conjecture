import AW3Sqrt

noncomputable section

open Grad.PDEBootstrap
open scoped ContDiff RealInnerProductSpace

namespace Grad.AnalyticWeights.Higher

theorem profileQuadratic_hasFDerivAt (point : Spatial) :
    HasFDerivAt profileQuadratic ((2 : ℝ) • innerSL ℝ point) point := by
  apply ((hasStrictFDerivAt_norm_sq point).hasFDerivAt.const_add 1).congr_fderiv
  apply ContinuousLinearMap.ext
  intro direction
  simp only [two_smul, add_apply]

theorem profileQuadratic_fderiv : fderiv ℝ profileQuadratic = fun point => (2 : ℝ) • innerSL ℝ point :=
  funext (fun point => (profileQuadratic_hasFDerivAt point).fderiv)

def quadraticBilinear : Spatial →L[ℝ] Spatial →L[ℝ] ℝ := (2 : ℝ) • innerSL ℝ

theorem profileQuadratic_second (point : Spatial) :
    fderiv ℝ (fderiv ℝ profileQuadratic) point = quadraticBilinear := by
  rw [profileQuadratic_fderiv]
  exact quadraticBilinear.fderiv

theorem profileQuadratic_iterated_two :
    iteratedFDeriv ℝ 2 profileQuadratic = fun _ =>
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => Spatial) ℝ).symm
        ((continuousMultilinearCurryFin1 ℝ Spatial ℝ).symm.toContinuousLinearMap.comp
          quadraticBilinear) := by
  funext point
  apply ContinuousMultilinearMap.ext
  intro directions
  rw [iteratedFDeriv_two_apply, profileQuadratic_second]
  rfl

theorem profileQuadratic_high_zero (rank : ℕ) :
    iteratedFDeriv ℝ (rank + 3) profileQuadratic = 0 := by
  induction rank with
  | zero =>
    rw [show 0 + 3 = 2 + 1 from rfl, iteratedFDeriv_succ_eq_comp_left,
      profileQuadratic_iterated_two]
    simp
    apply ContinuousMultilinearMap.ext
    intro directions
    rfl
  | succ rank inductionHypothesis =>
    rw [show rank + 1 + 3 = (rank + 3) + 1 by omega, iteratedFDeriv_succ_eq_comp_left,
      inductionHypothesis]
    simp
    apply ContinuousMultilinearMap.ext
    intro directions
    rfl

theorem profileQuadratic_iterated_norm_bound (rank : ℕ) (positiveRank : 1 ≤ rank) (point : Spatial) :
    ‖iteratedFDeriv ℝ rank profileQuadratic point‖ ≤
      2 * profileQuadratic point / Real.sqrt (profileQuadratic point) ^ rank := by
  have rootPositive := Real.sqrt_pos.mpr (profileQuadratic_pos point)
  have rootSquare := Real.sq_sqrt (profileQuadratic_pos point).le
  have normBound : ‖point‖ ≤ Real.sqrt (profileQuadratic point) := by
    apply Real.le_sqrt_of_sq_le
    unfold profileQuadratic
    linarith
  rcases rank with _ | rank
  · omega
  rcases rank with _ | rank
  · rw [norm_iteratedFDeriv_one, profileQuadratic_fderiv]
    change ‖(2 : ℝ) • innerSL ℝ point‖ ≤ 2 * profileQuadratic point / Real.sqrt (profileQuadratic point) ^ 1
    rw [norm_smul, Real.norm_ofNat, innerSL_apply_norm, pow_one]
    apply (le_div_iff₀ rootPositive).mpr
    nlinarith
  rcases rank with _ | rank
  · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one, profileQuadratic_second]
    have normSecond : ‖quadraticBilinear‖ ≤ 2 := by
      apply quadraticBilinear.opNorm_le_bound (by norm_num)
      intro first
      apply (quadraticBilinear first).opNorm_le_bound (by positivity)
      intro second
      change ‖(2 : ℝ) * inner ℝ first second‖ ≤ (2 * ‖first‖) * ‖second‖
      rw [norm_mul, Real.norm_ofNat, mul_assoc]
      exact mul_le_mul_of_nonneg_left (norm_inner_le_norm first second) (by norm_num)
    apply normSecond.trans
    rw [rootSquare, mul_div_cancel_right₀ _ (profileQuadratic_pos point).ne']
  · rw [show rank + 1 + 1 + 1 = rank + 3 by omega, profileQuadratic_high_zero]
    simp only [Pi.zero_apply, norm_zero]
    exact div_nonneg (mul_nonneg (by norm_num) (profileQuadratic_pos point).le)
      (pow_nonneg (Real.sqrt_nonneg _) _)

end Grad.AnalyticWeights.Higher
