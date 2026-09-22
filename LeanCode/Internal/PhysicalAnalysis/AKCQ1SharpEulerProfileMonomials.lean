import AKH1ActualPhaseSlopeJets
import AW3Profile

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.AnnularWeightedSmoothness
open Grad.AnalyticWeights.Calculus Grad.AnalyticWeights.Higher

/-- The exact square-root profile along the unit physical radial ray. -/
def eulerProfileRay (point : ℝ) : ℝ := profile (phaseRadialRay point)

theorem eulerProfileRay_smooth : ContDiff ℝ ∞ eulerProfileRay :=
  profile_contDiff.comp phaseRadialRay.contDiff

theorem phaseRadialRay_apply_norm (point : ℝ) : ‖phaseRadialRay point‖ = |point| := by
  simp [phaseRadialRay, ContinuousLinearMap.toSpanSingleton_apply, norm_smul,
    Real.norm_eq_abs, spatialBasis, PiLp.norm_single]

/-- Keep AW3's denominator: a coarse derivative bound would lose one input
cell derivative for each subsequent Euler differentiation. -/
theorem eulerProfileRay_iterated_decay (rank : ℕ) (positiveRank : 1 ≤ rank) (point : ℝ) :
    ‖iteratedDeriv rank eulerProfileRay point‖ ≤
      profileConstant rank / Real.sqrt (1 + point^2)^(rank-1) := by
  apply (radialRay_iteratedDeriv_bound profile profile_contDiff rank point).trans
  simpa only [phaseRadialRay_apply_norm, sq_abs] using
    profile_iterated_norm_decay rank positiveRank (phaseRadialRay point)

theorem eulerProfileRay_weighted_derivative (rank : ℕ) (positiveRank : 1 ≤ rank) (point : ℝ) :
    |point|^(rank-1)*‖iteratedDeriv rank eulerProfileRay point‖ ≤ profileConstant rank := by
  have rootPositive : 0 < Real.sqrt (1 + point^2) := Real.sqrt_pos.mpr (by positivity)
  have rootBound : |point| ≤ Real.sqrt (1 + point^2) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [sq_abs point])
  calc
    _ ≤ |point|^(rank-1)*(profileConstant rank / Real.sqrt (1 + point^2)^(rank-1)) :=
      mul_le_mul_of_nonneg_left (eulerProfileRay_iterated_decay rank positiveRank point) (by positivity)
    _ ≤ Real.sqrt (1 + point^2)^(rank-1)*
        (profileConstant rank / Real.sqrt (1 + point^2)^(rank-1)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg point) rootBound _)
        (div_nonneg (profileConstant_nonnegative _) (by positivity))
    _ = _ := by
      rw [mul_comm,div_mul_cancel₀ _ (pow_ne_zero _ rootPositive.ne')]

/-- The finite Euler expansion uses only t^j f^(j)(t), with j positive. -/
def eulerRayMonomial (rank : ℕ) (point : ℝ) : ℝ :=
  point^rank * iteratedDeriv rank eulerProfileRay point

def eulerRayMonomialDerivative (rank : ℕ) (point : ℝ) : ℝ :=
  (rank : ℝ)*point^(rank-1)*iteratedDeriv rank eulerProfileRay point +
    point^rank*iteratedDeriv (rank+1) eulerProfileRay point

theorem eulerRayMonomial_hasDerivAt (rank : ℕ) (point : ℝ) :
    HasDerivAt (eulerRayMonomial rank) (eulerRayMonomialDerivative rank point) point := by
  change HasDerivAt (fun location : ℝ => location^rank * iteratedDeriv rank eulerProfileRay location) _ point
  apply (((hasDerivAt_id point).pow rank).mul
    (smoothCurve_iteratedDeriv_hasDerivAt eulerProfileRay eulerProfileRay_smooth rank point)).congr_deriv
  simp only [eulerRayMonomialDerivative,Pi.pow_apply,id_eq,mul_one]

theorem eulerRayMonomial_bound (rank : ℕ) (positiveRank : 1 ≤ rank) (point : ℝ) :
    ‖eulerRayMonomial rank point‖ ≤ profileConstant rank*|point| := by
  have split : |point|^rank = |point| * |point|^(rank-1) := by
    rw [mul_comm,← pow_succ,Nat.sub_add_cancel positiveRank]
  rw [eulerRayMonomial,norm_mul,norm_pow,Real.norm_eq_abs,split,mul_assoc]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (eulerProfileRay_weighted_derivative rank positiveRank point) (abs_nonneg point)

/-- Every positive weighted profile monomial has a uniformly bounded first
spectral derivative. The constant has no cell or radius dependence. -/
theorem eulerRayMonomialDerivative_bound (rank : ℕ) (positiveRank : 1 ≤ rank) (point : ℝ) :
    ‖eulerRayMonomialDerivative rank point‖ ≤ spectralConstant rank := by
  have first := eulerProfileRay_weighted_derivative rank positiveRank point
  have second : |point|^rank*‖iteratedDeriv (rank+1) eulerProfileRay point‖ ≤ profileConstant (rank+1) := by
    simpa only [Nat.add_sub_cancel] using
      eulerProfileRay_weighted_derivative (rank+1) (by omega) point
  calc
    _ ≤ ‖(rank : ℝ)*point^(rank-1)*iteratedDeriv rank eulerProfileRay point‖ +
        ‖point^rank*iteratedDeriv (rank+1) eulerProfileRay point‖ := norm_add_le _ _
    _ = (rank : ℝ)*(|point|^(rank-1)*‖iteratedDeriv rank eulerProfileRay point‖) +
        |point|^rank*‖iteratedDeriv (rank+1) eulerProfileRay point‖ := by
      rw [norm_mul,norm_mul,norm_mul,norm_pow,norm_pow,
        Real.norm_of_nonneg (Nat.cast_nonneg rank),Real.norm_eq_abs,mul_assoc]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left first (Nat.cast_nonneg rank)) second

end Grad.OriginalCartesianTameEstimate
