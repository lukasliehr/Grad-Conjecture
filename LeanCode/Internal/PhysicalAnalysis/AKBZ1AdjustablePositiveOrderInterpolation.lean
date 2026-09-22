import AKBX6ActualOriginalTwoSidedAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace Grad.OriginalCartesianTameEstimate

/-- The adjustable weighted AM-GM step in CT9. Positive coefficient order
is essential; no upper state norm or output grade enters the small ball. -/
theorem positiveOrder_adjustable_geometric
    (theta epsilon first second : ℝ) (thetaPositive : 0<theta) (thetaOne : theta≤1)
    (epsilonPositive : 0<epsilon) (firstNonnegative : 0≤first) (secondNonnegative : 0≤second) :
    first^(1-theta)*second^theta ≤
      epsilon*first+epsilon^(-(1-theta)/theta)*second := by
  have scaleNonnegative : 0≤epsilon^(-(1-theta)/theta) := Real.rpow_nonneg epsilonPositive.le _
  have exponent : (1-theta)+(-(1-theta)/theta)*theta=0 := by
    field_simp [ne_of_gt thetaPositive]
    ring
  have identity : (epsilon*first)^(1-theta)*(epsilon^(-(1-theta)/theta)*second)^theta=
      first^(1-theta)*second^theta := by
    rw [Real.mul_rpow epsilonPositive.le firstNonnegative,
      Real.mul_rpow scaleNonnegative secondNonnegative,←Real.rpow_mul epsilonPositive.le]
    calc
      _=(epsilon^(1-theta)*epsilon^((-(1-theta)/theta)*theta))*(first^(1-theta)*second^theta) := by ring
      _=_ := by rw [←Real.rpow_add epsilonPositive,exponent,Real.rpow_zero,one_mul]
  have bound := Real.geom_mean_le_arith_mean2_weighted
    (sub_nonneg.mpr thetaOne) thetaPositive.le
    (mul_nonneg epsilonPositive.le firstNonnegative) (mul_nonneg scaleNonnegative secondNonnegative)
    (by ring : (1-theta)+theta=1)
  rw [identity] at bound
  refine bound.trans (add_le_add ?_ ?_)
  · exact mul_le_of_le_one_left (mul_nonneg epsilonPositive.le firstNonnegative) (by linarith : 1-theta≤1)
  · exact mul_le_of_le_one_left (mul_nonneg scaleNonnegative secondNonnegative) thetaOne

/-- Fixed-grade multiplicative constants are absorbed by selecting an
estimate epsilon after the grade; the physical neighborhood is unchanged. -/
theorem positiveOrder_adjustable_constant
    (theta constant epsilon : ℝ) (thetaPositive : 0<theta) (thetaOne : theta≤1)
    (constantNonnegative : 0≤constant) (epsilonPositive : 0<epsilon) :
    ∃ remainder : ℝ, 0≤remainder ∧ ∀ first second : ℝ, 0≤first → 0≤second →
      constant*(first^(1-theta)*second^theta)≤epsilon*first+remainder*second := by
  let delta := epsilon/(constant+1)
  have deltaPositive : 0<delta := div_pos epsilonPositive (by linarith)
  refine ⟨constant*delta^(-(1-theta)/theta),mul_nonneg constantNonnegative (Real.rpow_nonneg deltaPositive.le _),?_⟩
  intro first second firstNonnegative secondNonnegative
  have bound := mul_le_mul_of_nonneg_left
    (positiveOrder_adjustable_geometric theta delta first second thetaPositive thetaOne deltaPositive firstNonnegative secondNonnegative)
    constantNonnegative
  have paid : constant*delta≤epsilon := by
    dsimp only [delta]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0<constant+1)).mpr
    nlinarith
  calc
    _≤constant*(delta*first+delta^(-(1-theta)/theta)*second) := bound
    _=(constant*delta)*first+(constant*delta^(-(1-theta)/theta))*second := by ring
    _≤_ := by
      have step := mul_le_mul_of_nonneg_right paid firstNonnegative
      linarith only [step]

end Grad.OriginalCartesianTameEstimate
