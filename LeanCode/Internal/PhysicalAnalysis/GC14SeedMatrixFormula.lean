import GC14SeedConstants

noncomputable section

set_option maxHeartbeats 800000

namespace Grad.GaugeCoefficients.Physical.Frame

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GeometryClosure

def seedIsotropic (rho : ℝ) : ℝ := (Real.sqrt (1 + rho) + Real.sqrt (1 - rho)) / 2

def seedAnisotropic (rho : ℝ) : ℝ := (Real.sqrt (1 + rho) - Real.sqrt (1 - rho)) / 2

theorem seed_sqrt_difference_bound {argument : ℝ} (domain : 0 ≤ 1 + argument) :
    |Real.sqrt (1 + argument) - 1| ≤ |argument| := by
  have factor : (Real.sqrt (1 + argument) - 1) *
      (Real.sqrt (1 + argument) + 1) = argument := by
    nlinarith [Real.sq_sqrt domain]
  have bound := mul_le_mul_of_nonneg_left
    (show (1 : ℝ) ≤ Real.sqrt (1 + argument) + 1 by linarith [Real.sqrt_nonneg (1 + argument)])
    (abs_nonneg (Real.sqrt (1 + argument) - 1))
  rw [mul_one, ← abs_of_nonneg (show 0 ≤ Real.sqrt (1 + argument) + 1 by positivity),
    ← abs_mul, factor] at bound
  exact bound

theorem seed_shape_factors_bound {rho : ℝ} (small : |rho| ≤ 1) :
    |seedIsotropic rho - 1| ≤ |rho| ∧ |seedAnisotropic rho| ≤ |rho| := by
  have rhoRange := abs_le.mp small
  have plus := seed_sqrt_difference_bound (argument := rho) (by linarith)
  have minus := seed_sqrt_difference_bound (argument := -rho) (by linarith)
  simp only [← sub_eq_add_neg, abs_neg] at minus
  have sumBound := abs_add_le (Real.sqrt (1 + rho) - 1) (Real.sqrt (1 - rho) - 1)
  have differenceBound := abs_add_le (Real.sqrt (1 + rho) - 1) (-(Real.sqrt (1 - rho) - 1))
  simp only [← sub_eq_add_neg, abs_neg] at differenceBound
  constructor
  · have identity : seedIsotropic rho - 1 =
        ((Real.sqrt (1 + rho) - 1) + (Real.sqrt (1 - rho) - 1)) / 2 := by
      unfold seedIsotropic
      ring
    rw [identity, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  · have identity : seedAnisotropic rho =
        ((Real.sqrt (1 + rho) - 1) - (Real.sqrt (1 - rho) - 1)) / 2 := by
      unfold seedAnisotropic
      ring
    rw [identity, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith

theorem seed_matrix_double_angle (rho angle : ℝ) :
    seedMatrix rho angle =
      !![seedIsotropic rho + seedAnisotropic rho * Real.cos (2 * angle),
        seedAnisotropic rho * Real.sin (2 * angle);
        seedAnisotropic rho * Real.sin (2 * angle),
        seedIsotropic rho - seedAnisotropic rho * Real.cos (2 * angle)] := by
  unfold seedMatrix
  rw [rotatedDiagonal_entries]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [seedIsotropic, seedAnisotropic, Real.cos_two_mul, Real.sin_two_mul]
  all_goals nlinarith [
    congrArg (fun value : ℝ => Real.sqrt (1 - rho) * value) (Real.sin_sq_add_cos_sq angle),
    congrArg (fun value : ℝ => Real.sqrt (1 + rho) * value) (Real.sin_sq_add_cos_sq angle)]

theorem seed_harmonic_double_angle (rho alpha delta parameter angle : ℝ) :
    harmonicSeedMatrix rho alpha delta parameter angle =
      !![seedIsotropic rho + seedAnisotropic rho *
          Real.cos (2 * seedAngle alpha delta parameter angle),
        seedAnisotropic rho * Real.sin (2 * seedAngle alpha delta parameter angle);
        seedAnisotropic rho * Real.sin (2 * seedAngle alpha delta parameter angle),
        seedIsotropic rho - seedAnisotropic rho *
          Real.cos (2 * seedAngle alpha delta parameter angle)] :=
  seed_matrix_double_angle rho _

end Grad.GaugeCoefficients.Physical.Frame
