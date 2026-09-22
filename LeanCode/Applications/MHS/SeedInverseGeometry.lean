import SeedBasicBounds

noncomputable section

namespace Grad.Constraints.Seed

open Grad.GeometryClosure

theorem rotatedDiagonal_smul (scalar first second angle : ℝ) :
    rotatedDiagonal (scalar * first) (scalar * second) angle = scalar • rotatedDiagonal first second angle := by
  rw [rotatedDiagonal_entries, rotatedDiagonal_entries]
  ext row column
  fin_cases row <;> fin_cases column <;> simp <;> ring

theorem seed_inverse_reflected {rho : ℝ} (domain : |rho| < 1) (angle : ℝ) :
    seedInverse rho angle = (Real.sqrt (1 - rho ^ 2))⁻¹ • seedMatrix (-rho) angle := by
  have interval := abs_lt.mp domain
  have positive := seed_diagonal_positive interval.1 interval.2
  have determinant : Real.sqrt (1 - rho ^ 2) = Real.sqrt (1 + rho) * Real.sqrt (1 - rho) := by
    rw [← Real.sqrt_mul (by linarith : 0 ≤ 1 + rho)]
    congr 1
    ring
  rw [seedMatrix, ← rotatedDiagonal_smul]
  unfold seedInverse
  simp only [sub_neg_eq_add]
  congr 1
  · rw [show 1 + -rho = 1 - rho by ring, determinant]
    field_simp [positive.1.ne', positive.2.ne']
  · rw [determinant]
    field_simp [positive.1.ne', positive.2.ne']

theorem determinant_inverse_bound {eccentricity rho : ℝ}
    (nonnegative : 0 ≤ eccentricity) (small : eccentricity < 1) (rhoBound : |rho| ≤ eccentricity) :
    0 < Real.sqrt (1 - rho ^ 2) ∧
    (Real.sqrt (1 - rho ^ 2))⁻¹ ≤ (Real.sqrt (1 - eccentricity ^ 2))⁻¹ := by
  have squareBound : rho ^ 2 ≤ eccentricity ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg rho) nonnegative).mpr rhoBound
  have patchPositive : 0 < 1 - eccentricity ^ 2 := by nlinarith
  have positive := Real.sqrt_pos.mpr (show 0 < 1 - rho ^ 2 by linarith)
  refine ⟨positive, ?_⟩
  exact (inv_le_inv₀ positive (Real.sqrt_pos.mpr patchPositive)).mpr (Real.sqrt_le_sqrt (by linarith))

end Grad.Constraints.Seed
