import AAT6SameInverseCommutation
import ASG41InsertedSourceWeights

noncomputable section
set_option maxHeartbeats 800000

namespace Grad.AnnularGrades

open Grad.AnnularVariational

/-- The already accepted literal split weight with exactly one inserted
nu^t factor. The original analytic phase is unchanged. -/
def annularGradeWeight (angular cell inserted : ℕ) (mode : HighAnnularMode) : ℝ :=
  Grad.AnnularSourceGraph.sourceInsertedWeight angular cell inserted mode.val

theorem annularGradeWeight_literal (angular cell inserted : ℕ) (mode : HighAnnularMode) :
    annularGradeWeight angular cell inserted mode =
      (1 + |(mode.val.1 : ℝ)| + |(mode.val.2 : ℝ)|) ^ inserted *
        ((1 + |(mode.val.1 : ℝ)|) ^ angular * (1 + |(mode.val.2 : ℝ)|) ^ cell) := rfl

theorem annularGradeWeight_pos (angular cell inserted : ℕ) (mode : HighAnnularMode) :
    0 < annularGradeWeight angular cell inserted mode :=
  Grad.AnnularSourceGraph.sourceInsertedWeight_pos angular cell inserted mode.val

theorem annularGradeWeight_one_le (angular cell inserted : ℕ) (mode : HighAnnularMode) :
    1 ≤ annularGradeWeight angular cell inserted mode := by
  rw [annularGradeWeight_literal]
  have angularOne : (1 : ℝ) ≤ 1 + |(mode.val.1 : ℝ)| := by linarith [abs_nonneg (mode.val.1 : ℝ)]
  have cellOne : (1 : ℝ) ≤ 1 + |(mode.val.2 : ℝ)| := by linarith [abs_nonneg (mode.val.2 : ℝ)]
  have frequencyOne : (1 : ℝ) ≤ 1 + |(mode.val.1 : ℝ)| + |(mode.val.2 : ℝ)| := by
    linarith [abs_nonneg (mode.val.1 : ℝ), abs_nonneg (mode.val.2 : ℝ)]
  have first := one_le_pow₀ (n := angular) angularOne
  have second := one_le_pow₀ (n := cell) cellOne
  have third := one_le_pow₀ (n := inserted) frequencyOne
  nlinarith [mul_le_mul first second (by norm_num : (0 : ℝ) ≤ 1) (zero_le_one.trans first)]

theorem annularGradeWeight_zero (mode : HighAnnularMode) : annularGradeWeight 0 0 0 mode = 1 := by
  rw [annularGradeWeight_literal]
  simp only [pow_zero, mul_one]

theorem annularGradeWeight_add (angular cell inserted angularExtra cellExtra insertedExtra : ℕ)
    (mode : HighAnnularMode) :
    annularGradeWeight (angular + angularExtra) (cell + cellExtra) (inserted + insertedExtra) mode =
      annularGradeWeight angular cell inserted mode * annularGradeWeight angularExtra cellExtra insertedExtra mode := by
  simp only [annularGradeWeight_literal, pow_add]
  ring

theorem annularGradeWeight_mono (angular cell inserted largerAngular largerCell largerInserted : ℕ)
    (angularLe : angular ≤ largerAngular) (cellLe : cell ≤ largerCell) (insertedLe : inserted ≤ largerInserted)
    (mode : HighAnnularMode) :
    annularGradeWeight angular cell inserted mode ≤ annularGradeWeight largerAngular largerCell largerInserted mode := by
  rw [annularGradeWeight_literal, annularGradeWeight_literal]
  have angularOne : (1 : ℝ) ≤ 1 + |(mode.val.1 : ℝ)| := by linarith [abs_nonneg (mode.val.1 : ℝ)]
  have cellOne : (1 : ℝ) ≤ 1 + |(mode.val.2 : ℝ)| := by linarith [abs_nonneg (mode.val.2 : ℝ)]
  have frequencyOne : (1 : ℝ) ≤ 1 + |(mode.val.1 : ℝ)| + |(mode.val.2 : ℝ)| := by
    linarith [abs_nonneg (mode.val.1 : ℝ), abs_nonneg (mode.val.2 : ℝ)]
  exact mul_le_mul (pow_le_pow_right₀ frequencyOne insertedLe)
    (mul_le_mul (pow_le_pow_right₀ angularOne angularLe) (pow_le_pow_right₀ cellOne cellLe)
      (pow_nonneg (zero_le_one.trans cellOne) _) (pow_nonneg (zero_le_one.trans angularOne) _))
    (mul_nonneg (pow_nonneg (zero_le_one.trans angularOne) _) (pow_nonneg (zero_le_one.trans cellOne) _))
    (pow_nonneg (zero_le_one.trans frequencyOne) _)

theorem annularGradeWeight_inv_bound (angular cell inserted : ℕ) (mode : HighAnnularMode) :
    |(annularGradeWeight angular cell inserted mode)⁻¹| ≤ 1 := by
  rw [abs_of_pos (inv_pos.mpr (annularGradeWeight_pos angular cell inserted mode))]
  simpa only [one_div] using
    (div_le_one (annularGradeWeight_pos angular cell inserted mode)).2
      (annularGradeWeight_one_le angular cell inserted mode)

theorem annularGradeWeight_ratio_bound (angular cell inserted largerAngular largerCell largerInserted : ℕ)
    (angularLe : angular ≤ largerAngular) (cellLe : cell ≤ largerCell) (insertedLe : inserted ≤ largerInserted)
    (mode : HighAnnularMode) :
    |annularGradeWeight angular cell inserted mode / annularGradeWeight largerAngular largerCell largerInserted mode| ≤ 1 := by
  rw [abs_of_pos (div_pos (annularGradeWeight_pos angular cell inserted mode)
    (annularGradeWeight_pos largerAngular largerCell largerInserted mode))]
  exact (div_le_one (annularGradeWeight_pos largerAngular largerCell largerInserted mode)).2
    (annularGradeWeight_mono angular cell inserted largerAngular largerCell largerInserted angularLe cellLe insertedLe mode)

end Grad.AnnularGrades
