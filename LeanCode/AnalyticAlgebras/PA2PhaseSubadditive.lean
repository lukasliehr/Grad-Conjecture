import PA1PhaseWeights

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.PhaseAlgebra

open Grad.CartesianState

/-- The concave gap is monotone on the nonnegative axis. -/
theorem concaveGap_monotone (s t : ℝ) (sNonneg : 0 ≤ s) (le : s ≤ t) :
    concaveGap s ≤ concaveGap t := by
  unfold concaveGap
  have tNonneg : 0 ≤ t := le_trans sNonneg le
  have sqrtS := Real.sq_sqrt (show (0:ℝ) ≤ 1 + s ^ 2 by positivity)
  have sqrtT := Real.sq_sqrt (show (0:ℝ) ≤ 1 + t ^ 2 by positivity)
  have sGe := le_sqrt_one_add_sq s sNonneg
  have tGe := le_sqrt_one_add_sq t tNonneg
  have oneS := one_le_sqrt_one_add_sq s
  have oneT := one_le_sqrt_one_add_sq t
  have denomPos : 0 < Real.sqrt (1 + t ^ 2) + Real.sqrt (1 + s ^ 2) := by linarith
  have diffId : (Real.sqrt (1 + t ^ 2) - Real.sqrt (1 + s ^ 2)) *
      (Real.sqrt (1 + t ^ 2) + Real.sqrt (1 + s ^ 2)) = t ^ 2 - s ^ 2 := by
    have expand : (Real.sqrt (1 + t ^ 2) - Real.sqrt (1 + s ^ 2)) *
        (Real.sqrt (1 + t ^ 2) + Real.sqrt (1 + s ^ 2)) =
        Real.sqrt (1 + t ^ 2) ^ 2 - Real.sqrt (1 + s ^ 2) ^ 2 := by ring
    rw [expand, sqrtT, sqrtS]
    ring
  have boundId : t ^ 2 - s ^ 2 ≤ (t - s) *
      (Real.sqrt (1 + t ^ 2) + Real.sqrt (1 + s ^ 2)) := by
    have factor : t ^ 2 - s ^ 2 = (t - s) * (t + s) := by ring
    rw [factor]
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr le)
    linarith
  have key : Real.sqrt (1 + t ^ 2) - Real.sqrt (1 + s ^ 2) ≤ t - s :=
    le_of_mul_le_mul_right (by rw [diffId]; exact boundId) denomPos
  linarith

/-- The concave gap is subadditive on the nonnegative axis. -/
theorem concaveGap_subadditive (x y : ℝ) (xNonneg : 0 ≤ x) (yNonneg : 0 ≤ y) :
    concaveGap (x + y) ≤ concaveGap x + concaveGap y := by
  unfold concaveGap
  have Ax := sqrt_one_add_sq_le x xNonneg
  have Ay := sqrt_one_add_sq_le y yNonneg
  have oneX := one_le_sqrt_one_add_sq x
  have oneY := one_le_sqrt_one_add_sq y
  have sqX := Real.sq_sqrt (show (0:ℝ) ≤ 1 + x ^ 2 by positivity)
  have sqY := Real.sq_sqrt (show (0:ℝ) ≤ 1 + y ^ 2 by positivity)
  have sqZ := Real.sq_sqrt (show (0:ℝ) ≤ 1 + (x + y) ^ 2 by positivity)
  have productLe : (Real.sqrt (1 + x ^ 2) - 1) * (Real.sqrt (1 + y ^ 2) - 1) ≤
      x * y :=
    mul_le_mul (by linarith) (by linarith) (by linarith) xNonneg
  have squareLe : (Real.sqrt (1 + x ^ 2) + Real.sqrt (1 + y ^ 2) - 1) ^ 2 ≤
      Real.sqrt (1 + (x + y) ^ 2) ^ 2 := by nlinarith
  have baseNonneg : 0 ≤ Real.sqrt (1 + x ^ 2) + Real.sqrt (1 + y ^ 2) - 1 := by
    linarith
  have key : Real.sqrt (1 + x ^ 2) + Real.sqrt (1 + y ^ 2) - 1 ≤
      Real.sqrt (1 + (x + y) ^ 2) := by
    calc Real.sqrt (1 + x ^ 2) + Real.sqrt (1 + y ^ 2) - 1
        = Real.sqrt ((Real.sqrt (1 + x ^ 2) + Real.sqrt (1 + y ^ 2) - 1) ^ 2) :=
          (Real.sqrt_sq baseNonneg).symm
      _ ≤ Real.sqrt (Real.sqrt (1 + (x + y) ^ 2) ^ 2) := Real.sqrt_le_sqrt squareLe
      _ = Real.sqrt (1 + (x + y) ^ 2) := Real.sqrt_sq (Real.sqrt_nonneg _)
  linarith

/-- The frequency is subadditive over cell addition. -/
theorem cellFrequency_subadditive (n m : ℤ) :
    cellFrequency (n + m) ≤ cellFrequency n + cellFrequency m := by
  rw [cellFrequency_formula, cellFrequency_formula, cellFrequency_formula]
  have geN : |(n : ℝ)| ≤ Real.sqrt (1 + (n : ℝ) ^ 2) := by
    have := le_sqrt_one_add_sq |(n : ℝ)| (abs_nonneg _)
    rwa [sq_abs] at this
  have geM : |(m : ℝ)| ≤ Real.sqrt (1 + (m : ℝ) ^ 2) := by
    have := le_sqrt_one_add_sq |(m : ℝ)| (abs_nonneg _)
    rwa [sq_abs] at this
  have nonnegN := Real.sqrt_nonneg (1 + (n : ℝ) ^ 2)
  have nonnegM := Real.sqrt_nonneg (1 + (m : ℝ) ^ 2)
  have sqN := Real.sq_sqrt (show (0:ℝ) ≤ 1 + (n : ℝ) ^ 2 by positivity)
  have sqM := Real.sq_sqrt (show (0:ℝ) ≤ 1 + (m : ℝ) ^ 2 by positivity)
  have productGe : |(n : ℝ)| * |(m : ℝ)| ≤
      Real.sqrt (1 + (n : ℝ) ^ 2) * Real.sqrt (1 + (m : ℝ) ^ 2) :=
    mul_le_mul geN geM (abs_nonneg _) nonnegN
  have absProduct : (n : ℝ) * (m : ℝ) ≤ |(n : ℝ)| * |(m : ℝ)| := by
    calc (n : ℝ) * (m : ℝ) ≤ |(n : ℝ) * (m : ℝ)| := le_abs_self _
      _ = |(n : ℝ)| * |(m : ℝ)| := abs_mul _ _
  have squareLe : (1 + ((n : ℝ) + (m : ℝ)) ^ 2) ≤
      (Real.sqrt (1 + (n : ℝ) ^ 2) + Real.sqrt (1 + (m : ℝ) ^ 2)) ^ 2 := by
    nlinarith
  have push : ((n + m : ℤ) : ℝ) = (n : ℝ) + (m : ℝ) := by push_cast; ring
  rw [push]
  calc Real.sqrt (1 + ((n : ℝ) + (m : ℝ)) ^ 2)
      ≤ Real.sqrt ((Real.sqrt (1 + (n : ℝ) ^ 2) + Real.sqrt (1 + (m : ℝ) ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt squareLe
    _ = Real.sqrt (1 + (n : ℝ) ^ 2) + Real.sqrt (1 + (m : ℝ) ^ 2) :=
        Real.sqrt_sq (by linarith)

/-- B3: the manuscript phase is subadditive at every admissible radius. -/
theorem radialPhase_subadditive (parameters : PhaseParameters) (radius : ℝ)
    (lower : 0 ≤ radius) (upper : radius ≤ 1) (n m : ℤ) :
    radialPhase parameters radius (n + m) ≤
      radialPhase parameters radius n + radialPhase parameters radius m := by
  rw [radialPhase_decompose, radialPhase_decompose, radialPhase_decompose]
  have widthNonneg := phaseWidth_nonneg parameters radius lower upper
  have gammaNonneg := parameters_gamma_nonnegative parameters
  have freqSub := cellFrequency_subadditive n m
  have widthTerm : phaseWidth parameters radius * cellFrequency (n + m) ≤
      phaseWidth parameters radius * (cellFrequency n + cellFrequency m) :=
    mul_le_mul_of_nonneg_left freqSub widthNonneg
  have gapMonotone : concaveGap (radius * cellFrequency (n + m)) ≤
      concaveGap (radius * (cellFrequency n + cellFrequency m)) := by
    apply concaveGap_monotone
    · exact mul_nonneg lower (cellFrequency_pos (n + m)).le
    · exact mul_le_mul_of_nonneg_left freqSub lower
  have gapSplit : concaveGap (radius * (cellFrequency n + cellFrequency m)) ≤
      concaveGap (radius * cellFrequency n) + concaveGap (radius * cellFrequency m) := by
    have expand : radius * (cellFrequency n + cellFrequency m) =
        radius * cellFrequency n + radius * cellFrequency m := by ring
    rw [expand]
    exact concaveGap_subadditive _ _ (mul_nonneg lower (cellFrequency_pos n).le)
      (mul_nonneg lower (cellFrequency_pos m).le)
  have gammaTerm : parameters.gamma * concaveGap (radius * cellFrequency (n + m)) ≤
      parameters.gamma * (concaveGap (radius * cellFrequency n) +
        concaveGap (radius * cellFrequency m)) :=
    mul_le_mul_of_nonneg_left (le_trans gapMonotone gapSplit) gammaNonneg
  have expandWidth : phaseWidth parameters radius *
      (cellFrequency n + cellFrequency m) =
      phaseWidth parameters radius * cellFrequency n +
        phaseWidth parameters radius * cellFrequency m := by ring
  have expandGamma : parameters.gamma * (concaveGap (radius * cellFrequency n) +
      concaveGap (radius * cellFrequency m)) =
      parameters.gamma * concaveGap (radius * cellFrequency n) +
        parameters.gamma * concaveGap (radius * cellFrequency m) := by ring
  linarith

/-- The B3 exponential ratio corollary. -/
theorem exp_radialPhase_ratio (parameters : PhaseParameters) (radius : ℝ)
    (lower : 0 ≤ radius) (upper : radius ≤ 1) (n m : ℤ) :
    Real.exp (radialPhase parameters radius n - radialPhase parameters radius m) ≤
      Real.exp (radialPhase parameters radius (n - m)) := by
  apply Real.exp_le_exp.mpr
  have subadd := radialPhase_subadditive parameters radius lower upper (n - m) m
  rw [sub_add_cancel] at subadd
  linarith

end Grad.PhaseAlgebra
