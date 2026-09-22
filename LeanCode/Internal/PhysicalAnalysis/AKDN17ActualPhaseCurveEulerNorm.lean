import AKDN16ActualNativeRowOneHigh

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothness Grad.AnnularKernelL2

/-- The original phase contribution to the actual radial equation has a
genuine Euler norm bound using exactly one higher native frequency grade.
The constant is independent of every coefficient state and input curve. -/
theorem actualPhaseCurve_EulerOneOrder {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (curve : ℕ → ℝ → CellL2 dimension)
    (smooth : ∀ power, ContDiffOn ℝ ∞ (curve power) (Icc lower 1))
    (same : ∀ power reserve radius, radius ∈ Icc lower 1 → ∀ mode,
      curve (power+reserve) radius mode=(annularFrequency mode.1 mode.2 : ℂ)^reserve • curve power radius mode)
    (grade rank : ℕ) (radius : RadialPoint) (inside : radius.val ∈ Icc lower 1) :
    ‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (fun point => balancedPhaseAction parameters dimension (collarRadius lower positive bounded.le point) (curve (grade+1) point)) radius.val‖ ≤
      eulerAllocationSum (fun order inputRank => balancedPhaseEulerConstant parameters order *
        ‖vectorEulerWithinIteratedDerivative (Icc lower 1) inputRank (curve (grade+1)) radius.val‖) (eulerLeibnizTerms rank) := by
  let reserve := rank+5
  let operator := balancedReservedPhaseAction parameters dimension (reserve+1)
  have operatorSmooth : ContDiffOn ℝ rank operator (Icc lower 1) :=
    balancedReservedPhaseAction_smooth parameters dimension (reserve+1) rank (by omega) lower bounded
  have original : EqOn
      (fun point => balancedPhaseAction parameters dimension (collarRadius lower positive bounded.le point) (curve (grade+1) point))
      (fun point => complexOperatorApply dimension dimension (operator point) (curve (grade+1+reserve) point)) (Icc lower 1) := by
    intro point member
    dsimp only
    have action := balancedReservedPhaseAction_sameEuler parameters dimension reserve 0 (by dsimp only [reserve]; omega)
      lower positive bounded (collarRadius lower positive bounded.le point)
      (by simpa only [collarRadius_literal lower positive bounded.le point member] using member)
      (curve (grade+1+reserve) point) (curve (grade+1) point) (same (grade+1) reserve point member)
    rw [balancedPhaseEulerAction_zero,collarRadius_literal lower positive bounded.le point member] at action
    exact action.symm
  rw [vectorEulerWithin_congr (Icc lower 1) rank _ _ original inside,
    vectorEulerWithin_bilinear (complexOperatorApply dimension dimension) (Icc lower 1) (uniqueDiffOn_Icc bounded)
      (fun point member => (positive.trans_le member.1).ne') operator (curve (grade+1+reserve)) rank
      operatorSmooth (contDiffOn_infty.mp (smooth _) rank) inside]
  apply (bilinearEulerPolynomial_norm (complexOperatorApply dimension dimension) _ _ _ radius.val).trans
  apply eulerAllocationSum_mono
  intro term member
  have allocated := eulerLeibnizTerms_rank rank term member
  change ‖vectorEulerWithinIteratedDerivative (Icc lower 1) term.1 operator radius.val
    (vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 (curve (grade+1+reserve)) radius.val)‖ ≤ _
  rw [balancedReservedPhaseAction_sameEuler parameters dimension reserve term.1 (by dsimp only [reserve]; omega)
    lower positive bounded radius inside
    (vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 (curve (grade+1+reserve)) radius.val)
    (vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 (curve (grade+1)) radius.val)
    (cellCurveEuler_shift lower bounded curve smooth same (grade+1) reserve term.2 radius.val inside)]
  exact ((balancedPhaseEulerAction parameters dimension term.1 radius).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (balancedPhaseEulerAction_norm parameters dimension term.1 radius) (norm_nonneg _))

end Grad.OriginalCartesianTameEstimate
