import AKDA5OrderedInverseEulerExpressions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.GaugeCoefficients.Physical.Allocation

/-- Each ordered expression pays its total physical rank only after all
factors and the displacement moment have been allocated. -/
def inverseExpressionMomentConstant (offset : ℕ) (inverseConstants : ℕ → ℝ)
    (forwardConstants : ℕ → ℕ → ℝ) : InverseEulerExpr → ℕ → ℝ :=
  InverseEulerExpr.rec inverseConstants (fun rank => forwardConstants (rank+1))
    (fun _ _ first second moment => first moment+second moment)
    (fun first second firstConstant secondConstant moment =>
      2^moment*(firstConstant moment*secondConstant 0+firstConstant 0*secondConstant moment)*
        (3+pairBudgetConstant offset (inverseEulerExprDegree first+inverseEulerExprDegree second+moment) 1))
    (fun _ previous => previous)

theorem inverseExpressionMomentConstant_nonnegative (offset : ℕ) (inverseConstants : ℕ → ℝ)
    (forwardConstants : ℕ → ℕ → ℝ) (inverse0 : ∀ moment, 0 ≤ inverseConstants moment)
    (forward0 : ∀ rank moment, 0 ≤ forwardConstants rank moment) (expression : InverseEulerExpr) :
    ∀ moment, 0 ≤ inverseExpressionMomentConstant offset inverseConstants forwardConstants expression moment := by
  induction expression with
  | inverse => exact inverse0
  | forward rank => exact forward0 (rank+1)
  | add first second first0 second0 => exact fun moment => add_nonneg (first0 moment) (second0 moment)
  | mul first second first0 second0 =>
      intro moment
      have pair0 := pairBudgetConstant_nonnegative offset
        (inverseEulerExprDegree first+inverseEulerExprDegree second+moment) (lowBound := (1 : ℝ)) zero_le_one
      exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) moment)
        (add_nonneg (mul_nonneg (first0 moment) (second0 0)) (mul_nonneg (first0 0) (second0 moment)))) (by linarith)
  | neg expression previous => exact previous

/-- Uniform ordered inverse-word moment allocation. The degree records
all primitive Euler derivatives, while every kernel retains its exact phase. -/
theorem inverseEulerExprKernel_joint_bound {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters 3) (rho epsilon : ℝ) (radius : RadialPoint) (offset : ℕ)
    (low : physicalBudget parameters field rho epsilon offset ≤ 1)
    (inverse : RadialKernel parameters radius dimension dimension)
    (forward : ℕ → RadialKernel parameters radius dimension dimension)
    (inverseConstants : ℕ → ℝ) (forwardConstants : ℕ → ℕ → ℝ)
    (inverse0 : ∀ moment, 0 ≤ inverseConstants moment)
    (forward0 : ∀ rank moment, 0 ≤ forwardConstants rank moment)
    (inverseBound : ∀ moment, fullKernelMoment (radialKernelParameters parameters radius) moment inverse ≤
      inverseConstants moment*(1+physicalBudget parameters field rho epsilon (offset+moment)))
    (forwardBound : ∀ rank moment, fullKernelMoment (radialKernelParameters parameters radius) moment (forward rank) ≤
      forwardConstants rank moment*(1+physicalBudget parameters field rho epsilon (offset+(rank+moment))))
    (expression : InverseEulerExpr) :
    ∀ moment, fullKernelMoment (radialKernelParameters parameters radius) moment
      (inverseEulerExprKernel inverse forward expression) ≤
      inverseExpressionMomentConstant offset inverseConstants forwardConstants expression moment *
        (1+physicalBudget parameters field rho epsilon (offset+(inverseEulerExprDegree expression+moment))) := by
  induction expression with
  | inverse =>
      intro moment
      simpa only [inverseEulerExprKernel,inverseExpressionMomentConstant,inverseEulerExprDegree,Nat.zero_add] using inverseBound moment
  | forward rank => exact forwardBound (rank+1)
  | add first second firstBound secondBound =>
      intro moment
      have first0 := inverseExpressionMomentConstant_nonnegative offset inverseConstants forwardConstants inverse0 forward0 first moment
      have second0 := inverseExpressionMomentConstant_nonnegative offset inverseConstants forwardConstants inverse0 forward0 second moment
      have firstPaid := (firstBound moment).trans (mul_le_mul_of_nonneg_left
        (add_le_add (le_refl (1 : ℝ)) (physicalBudget_monotone parameters field rho epsilon
          (show offset+(inverseEulerExprDegree first+moment) ≤
            offset+(max (inverseEulerExprDegree first) (inverseEulerExprDegree second)+moment) by omega))) first0)
      have secondPaid := (secondBound moment).trans (mul_le_mul_of_nonneg_left
        (add_le_add (le_refl (1 : ℝ)) (physicalBudget_monotone parameters field rho epsilon
          (show offset+(inverseEulerExprDegree second+moment) ≤
            offset+(max (inverseEulerExprDegree first) (inverseEulerExprDegree second)+moment) by omega))) second0)
      exact (fullKernelAdd_moment_le _ moment _ _).trans ((add_le_add firstPaid secondPaid).trans_eq (by
        change _ = (inverseExpressionMomentConstant offset inverseConstants forwardConstants first moment+
          inverseExpressionMomentConstant offset inverseConstants forwardConstants second moment)*
            (1+physicalBudget parameters field rho epsilon
              (offset+(max (inverseEulerExprDegree first) (inverseEulerExprDegree second)+moment)))
        ring))
  | mul first second firstBound secondBound =>
      intro moment
      let total := inverseEulerExprDegree first+inverseEulerExprDegree second+moment
      exact fullKernelComposition_joint_oneHigh parameters field rho epsilon radius offset total
        (inverseEulerExprDegree first) (inverseEulerExprDegree second) moment le_rfl low
        (inverseEulerExprKernel inverse forward first) (inverseEulerExprKernel inverse forward second)
        (inverseExpressionMomentConstant offset inverseConstants forwardConstants first moment)
        (inverseExpressionMomentConstant offset inverseConstants forwardConstants first 0)
        (inverseExpressionMomentConstant offset inverseConstants forwardConstants second moment)
        (inverseExpressionMomentConstant offset inverseConstants forwardConstants second 0)
        (inverseExpressionMomentConstant_nonnegative offset inverseConstants forwardConstants inverse0 forward0 first moment)
        (inverseExpressionMomentConstant_nonnegative offset inverseConstants forwardConstants inverse0 forward0 first 0)
        (inverseExpressionMomentConstant_nonnegative offset inverseConstants forwardConstants inverse0 forward0 second moment)
        (inverseExpressionMomentConstant_nonnegative offset inverseConstants forwardConstants inverse0 forward0 second 0)
        (firstBound moment) (by simpa only [Nat.add_zero] using firstBound 0)
        (secondBound moment) (by simpa only [Nat.add_zero] using secondBound 0)
  | neg expression previous =>
      intro moment
      exact (fullKernelNeg_moment_le _ moment _).trans (previous moment)

/-- All formal ordered inverse Euler words spend at most the requested
Euler rank plus the displacement moment, with a single high physical size. -/
theorem inverseEulerWords_oneHigh {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters 3) (rho epsilon : ℝ) (radius : RadialPoint) (offset : ℕ)
    (low : physicalBudget parameters field rho epsilon offset ≤ 1)
    (inverse : RadialKernel parameters radius dimension dimension)
    (forward : ℕ → RadialKernel parameters radius dimension dimension)
    (inverseConstants : ℕ → ℝ) (forwardConstants : ℕ → ℕ → ℝ)
    (inverse0 : ∀ moment, 0 ≤ inverseConstants moment)
    (forward0 : ∀ rank moment, 0 ≤ forwardConstants rank moment)
    (inverseBound : ∀ moment, fullKernelMoment (radialKernelParameters parameters radius) moment inverse ≤
      inverseConstants moment*(1+physicalBudget parameters field rho epsilon (offset+moment)))
    (forwardBound : ∀ raw moment, fullKernelMoment (radialKernelParameters parameters radius) moment (forward raw) ≤
      forwardConstants raw moment*(1+physicalBudget parameters field rho epsilon (offset+(raw+moment))))
    (rank moment : ℕ) :
    fullKernelMoment (radialKernelParameters parameters radius) moment
      (inverseEulerExprKernel inverse forward (inverseEulerExpression rank)) ≤
      inverseExpressionMomentConstant offset inverseConstants forwardConstants (inverseEulerExpression rank) moment *
        (1+physicalBudget parameters field rho epsilon (offset+(rank+moment))) := by
  have result := inverseEulerExprKernel_joint_bound parameters field rho epsilon radius offset low inverse forward
    inverseConstants forwardConstants inverse0 forward0 inverseBound forwardBound (inverseEulerExpression rank) moment
  exact result.trans (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl (1 : ℝ)) (physicalBudget_monotone parameters field rho epsilon
      (Nat.add_le_add_left (Nat.add_le_add_right (inverseEulerExpression_degree rank) moment) offset)))
    (inverseExpressionMomentConstant_nonnegative offset inverseConstants forwardConstants inverse0 forward0 _ _))

end Grad.OriginalCartesianTameEstimate
