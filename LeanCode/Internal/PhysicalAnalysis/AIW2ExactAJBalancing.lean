import AIW1OriginalAJClosedGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularOriginalLow
open Grad.AnnularLowEnergy Grad.CartesianState Grad.AnnularCurrentLow

/-- The exact original AJ6 damping minimum. -/
def originalLowDampingMinimum (parameters : PhaseParameters) (lower : ℝ) : ℝ :=
  parameters.gamma * lower / Real.sqrt (1 + lower ^ 2)

/-- Literal AJ6 center rescaling, made once at the inner radius. -/
def originalLowCenterScale (parameters : PhaseParameters) (lower length : ℝ) : ℝ :=
  1 + 2 / (originalLowDampingMinimum parameters lower * length ^ 2)

/-- The first diagonal entry of the ORIGINAL S_ell,m; the second is one. -/
def originalLowScale (parameters : PhaseParameters) (lower length : ℝ) (mode : LowAnnularMode) : ℝ :=
  if |mode.val.1| = 1 then (Real.sqrt 3 * length)⁻¹ else originalLowCenterScale parameters lower length

theorem originalLowDampingMinimum_positive (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) : 0 < originalLowDampingMinimum parameters lower := by
  have gamma := parameters.gamma_pos
  unfold originalLowDampingMinimum
  positivity

theorem originalLowCenterScale_one_le (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) : 1 ≤ originalLowCenterScale parameters lower length := by
  have damping := originalLowDampingMinimum_positive parameters lower positive
  unfold originalLowCenterScale
  have nonnegative : 0 ≤ 2 / (originalLowDampingMinimum parameters lower * length ^ 2) := by positivity
  linarith

theorem originalLowScale_positive (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (mode : LowAnnularMode) :
    0 < originalLowScale parameters lower length mode := by
  unfold originalLowScale
  split_ifs
  · positivity
  · exact zero_lt_one.trans_le (originalLowCenterScale_one_le parameters lower length positive lengthPositive)

def originalLowScaleConstant (parameters : PhaseParameters) (length : ℝ) : ℝ :=
  (Real.sqrt 3 * length)⁻¹ + 1 + 2 * Real.sqrt 2 / (parameters.gamma * length ^ 2)

theorem originalLowScaleConstant_positive (parameters : PhaseParameters) (length : ℝ)
    (lengthPositive : 0 < length) : 0 < originalLowScaleConstant parameters length := by
  have gamma := parameters.gamma_pos
  unfold originalLowScaleConstant
  positivity

theorem originalLowDampingMinimum_inverse_bound (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) :
    (originalLowDampingMinimum parameters lower)⁻¹ ≤ Real.sqrt 2 / parameters.gamma * lower⁻¹ := by
  have root : Real.sqrt (1 + lower ^ 2) ≤ Real.sqrt 2 :=
    Real.sqrt_le_sqrt (by nlinarith)
  have gamma := parameters.gamma_pos
  have inverse : (originalLowDampingMinimum parameters lower)⁻¹ =
      Real.sqrt (1 + lower ^ 2) / parameters.gamma * lower⁻¹ := by
    unfold originalLowDampingMinimum
    field_simp
  rw [inverse]
  gcongr

theorem originalLowScale_bound (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length) (mode : LowAnnularMode) :
    originalLowScale parameters lower length mode ≤ originalLowScaleConstant parameters length * lower⁻¹ := by
  have gamma := parameters.gamma_pos
  have inverseOne : 1 ≤ lower⁻¹ := (one_le_inv₀ positive).mpr bounded
  have first : 0 ≤ (Real.sqrt 3 * length)⁻¹ := by positivity
  have last : 0 ≤ 2 * Real.sqrt 2 / (parameters.gamma * length ^ 2) := by positivity
  unfold originalLowScale
  split_ifs
  · have compared : (Real.sqrt 3 * length)⁻¹ ≤ (Real.sqrt 3 * length)⁻¹ * lower⁻¹ :=
      by simpa only [mul_one] using mul_le_mul_of_nonneg_left inverseOne first
    unfold originalLowScaleConstant
    nlinarith [inv_pos.mpr positive]
  · have inverse := originalLowDampingMinimum_inverse_bound parameters lower positive bounded
    have scaled := mul_le_mul_of_nonneg_left inverse (show 0 ≤ 2 / length ^ 2 by positivity)
    have literal : originalLowCenterScale parameters lower length =
        1 + (2 / length ^ 2) * (originalLowDampingMinimum parameters lower)⁻¹ := by
      unfold originalLowCenterScale
      ring
    rw [literal]
    unfold originalLowScaleConstant
    have adjusted : (2 / length ^ 2) * (Real.sqrt 2 / parameters.gamma * lower⁻¹) =
        (2 * Real.sqrt 2 / (parameters.gamma * length ^ 2)) * lower⁻¹ := by ring
    rw [adjusted] at scaled
    nlinarith [mul_nonneg first (inv_nonneg.mpr positive.le)]

theorem originalLowScale_inverse_bound (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (mode : LowAnnularMode) :
    (originalLowScale parameters lower length mode)⁻¹ ≤ 1 + Real.sqrt 3 * length := by
  unfold originalLowScale
  split_ifs
  · rw [inv_inv]
    linarith
  · apply (inv_le_one_of_one_le₀ (originalLowCenterScale_one_le parameters lower length positive lengthPositive)).trans
    have nonnegative : 0 ≤ Real.sqrt 3 * length := by positivity
    linarith

end Grad.AnnularOriginalLow
