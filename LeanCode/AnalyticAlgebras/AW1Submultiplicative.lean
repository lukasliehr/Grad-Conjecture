import AW1Phase

noncomputable section

open Grad.PDEBootstrap

namespace Grad.AnalyticWeights

def spectralPhase (sigma gamma radius frequency : ℝ) : ℝ :=
  sigma * frequency - gamma * (Real.sqrt (1 + radius ^ 2 * frequency ^ 2) - 1)

theorem phase_eq_spectralPhase (sigma gamma radius : ℝ) (cell : ℤ) :
    phase sigma gamma radius cell = spectralPhase sigma gamma radius (Grad.CellWeights.cellWeight cell) := rfl

theorem sqrt_increment_bound (first second : ℝ) (nonnegative : 0 ≤ first) (ordered : first ≤ second) :
    Real.sqrt (1 + second ^ 2) - Real.sqrt (1 + first ^ 2) ≤ second - first := by
  have firstLower := (sqrt_one_add_sq_bounds first nonnegative).1
  have firstSquare := Real.sq_sqrt (show 0 ≤ 1 + first ^ 2 by positivity)
  have estimate : Real.sqrt (1 + second ^ 2) ≤ Real.sqrt (1 + first ^ 2) + (second - first) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [mul_nonneg (sub_nonneg.mpr ordered) (sub_nonneg.mpr firstLower)]
  linarith

theorem sqrt_superadditive_defect (first second : ℝ) (firstNonnegative : 0 ≤ first)
    (secondNonnegative : 0 ≤ second) :
    Real.sqrt (1 + first ^ 2) + Real.sqrt (1 + second ^ 2) ≤
      Real.sqrt (1 + (first + second) ^ 2) + 1 := by
  have firstBounds := sqrt_one_add_sq_bounds first firstNonnegative
  have secondBounds := sqrt_one_add_sq_bounds second secondNonnegative
  have firstOne : 1 ≤ Real.sqrt (1 + first ^ 2) := Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg first])
  have secondOne : 1 ≤ Real.sqrt (1 + second ^ 2) := Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg second])
  have productBound :
      (Real.sqrt (1 + first ^ 2) - 1) * (Real.sqrt (1 + second ^ 2) - 1) ≤ first * second :=
    mul_le_mul (by linarith [firstBounds.2]) (by linarith [secondBounds.2])
      (by linarith) firstNonnegative
  have firstSquare := Real.sq_sqrt (show 0 ≤ 1 + first ^ 2 by positivity)
  have secondSquare := Real.sq_sqrt (show 0 ≤ 1 + second ^ 2 by positivity)
  have estimate : Real.sqrt (1 + first ^ 2) + Real.sqrt (1 + second ^ 2) - 1 ≤
      Real.sqrt (1 + (first + second) ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  linarith

theorem spectralPhase_mono (sigma gamma radius first second : ℝ)
    (gammaNonnegative : 0 ≤ gamma) (radiusNonnegative : 0 ≤ radius)
    (rateNonnegative : 0 ≤ rate sigma gamma radius)
    (firstNonnegative : 0 ≤ first) (ordered : first ≤ second) :
    spectralPhase sigma gamma radius first ≤ spectralPhase sigma gamma radius second := by
  have rootIncrement := sqrt_increment_bound (radius * first) (radius * second)
    (mul_nonneg radiusNonnegative firstNonnegative) (mul_le_mul_of_nonneg_left ordered radiusNonnegative)
  simp only [mul_pow] at rootIncrement
  have scaledIncrement := mul_le_mul_of_nonneg_left rootIncrement gammaNonnegative
  have rateProduct := mul_nonneg rateNonnegative (sub_nonneg.mpr ordered)
  dsimp [spectralPhase]
  dsimp [rate] at rateProduct
  nlinarith

theorem spectralPhase_subadditive (sigma gamma radius first second : ℝ)
    (gammaNonnegative : 0 ≤ gamma) (radiusNonnegative : 0 ≤ radius)
    (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second) :
    spectralPhase sigma gamma radius (first + second) ≤
      spectralPhase sigma gamma radius first + spectralPhase sigma gamma radius second := by
  have rootBound := sqrt_superadditive_defect (radius * first) (radius * second)
    (mul_nonneg radiusNonnegative firstNonnegative) (mul_nonneg radiusNonnegative secondNonnegative)
  rw [← mul_add] at rootBound
  simp only [mul_pow] at rootBound
  have scaledBound := mul_le_mul_of_nonneg_left rootBound gammaNonnegative
  dsimp [spectralPhase]
  nlinarith

theorem cellWeight_add_le (first second : ℤ) :
    Grad.CellWeights.cellWeight (first + second) ≤
      Grad.CellWeights.cellWeight first + Grad.CellWeights.cellWeight second := by
  have firstBounds := cellWeight_bounds first
  have secondBounds := cellWeight_bounds second
  have productBound : (first : ℝ) * (second : ℝ) ≤
      Grad.CellWeights.cellWeight first * Grad.CellWeights.cellWeight second := by
    calc
      _ ≤ |(first : ℝ) * (second : ℝ)| := le_abs_self _
      _ = |(first : ℝ)| * |(second : ℝ)| := abs_mul _ _
      _ ≤ _ := mul_le_mul firstBounds.1 secondBounds.1 (abs_nonneg _)
        (Grad.CellWeights.cellWeight_pos first).le
  apply (sq_le_sq₀ (Grad.CellWeights.cellWeight_pos (first + second)).le
    (add_nonneg (Grad.CellWeights.cellWeight_pos first).le (Grad.CellWeights.cellWeight_pos second).le)).mp
  rw [Grad.CellBinomial.cellWeight_sq, Int.cast_add]
  nlinarith [Grad.CellBinomial.cellWeight_sq first, Grad.CellBinomial.cellWeight_sq second]

theorem phase_subadditive (sigma gamma radius : ℝ) (first second : ℤ)
    (gammaNonnegative : 0 ≤ gamma) (radiusNonnegative : 0 ≤ radius)
    (rateNonnegative : 0 ≤ rate sigma gamma radius) :
    phase sigma gamma radius (first + second) ≤ phase sigma gamma radius first + phase sigma gamma radius second := by
  simp only [phase_eq_spectralPhase]
  exact (spectralPhase_mono sigma gamma radius _ _ gammaNonnegative radiusNonnegative rateNonnegative
    (Grad.CellWeights.cellWeight_pos _).le (cellWeight_add_le first second)).trans
      (spectralPhase_subadditive sigma gamma radius _ _ gammaNonnegative radiusNonnegative
        (Grad.CellWeights.cellWeight_pos first).le (Grad.CellWeights.cellWeight_pos second).le)

theorem weight_submultiplicative (sigma gamma radius : ℝ) (first second : ℤ)
    (gammaNonnegative : 0 ≤ gamma) (radiusNonnegative : 0 ≤ radius)
    (rateNonnegative : 0 ≤ rate sigma gamma radius) :
    weight sigma gamma radius (first + second) ≤
      weight sigma gamma radius first * weight sigma gamma radius second := by
  simpa only [weight, Real.exp_add] using Real.exp_le_exp.mpr
    (phase_subadditive sigma gamma radius first second gammaNonnegative radiusNonnegative rateNonnegative)

end Grad.AnalyticWeights
