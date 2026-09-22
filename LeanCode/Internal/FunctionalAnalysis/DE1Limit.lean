import DE1Bounds

noncomputable section

open Filter
open scoped BigOperators Topology

namespace Grad.DiskExtension.Seeley

theorem finite_nonzero (cutoff index : ℕ) (retained : index ≤ cutoff) : finiteCoefficient cutoff index ≠ 0 := by
  intro zero
  have positive := finite_sign cutoff index retained
  rw [zero, mul_zero] at positive
  exact lt_irrefl _ positive

theorem finite_signed_absolute (cutoff index : ℕ) (retained : index ≤ cutoff) :
    (-1 : ℝ) ^ index * finiteCoefficient cutoff index = |finiteCoefficient cutoff index| := by
  have equality := abs_of_pos (finite_sign cutoff index retained)
  simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using equality.symm

theorem finite_eq_signed_absolute (cutoff index : ℕ) (retained : index ≤ cutoff) :
    finiteCoefficient cutoff index = (-1 : ℝ) ^ index * |finiteCoefficient cutoff index| := by
  have signSquared : (-1 : ℝ) ^ index * (-1 : ℝ) ^ index = 1 := by rw [← mul_pow]; norm_num
  calc
    _ = ((-1 : ℝ) ^ index * (-1 : ℝ) ^ index) * finiteCoefficient cutoff index := by rw [signSquared, one_mul]
    _ = _ := by rw [mul_assoc, finite_signed_absolute cutoff index retained]

theorem next_factor_one_le (cutoff index : ℕ) (retained : index ≤ cutoff) :
    1 ≤ (1 + node (cutoff + 1)) / (node (cutoff + 1) - node index) := by
  apply (le_div_iff₀ (sub_pos.mpr (node_strictMono (by omega)))).mpr
  linarith [node_positive index]

theorem amplitude_monotone (index : ℕ) : Monotone (fun offset => |finiteCoefficient (index + offset) index|) := by
  apply monotone_nat_of_le_succ
  intro offset
  rw [show index + (offset + 1) = (index + offset) + 1 by omega,
    finite_succ (index + offset) index (by omega), abs_mul]
  have bound := next_factor_one_le (index + offset) index (by omega)
  rw [abs_of_pos (by linarith : 0 < (1 + node (index + offset + 1)) /
    (node (index + offset + 1) - node index))]
  exact le_mul_of_one_le_right (abs_nonneg _) bound

theorem amplitude_bounded (index : ℕ) :
    BddAbove (Set.range (fun offset => |finiteCoefficient (index + offset) index|)) :=
  ⟨coefficientBound index, fun _ ⟨offset, equality⟩ => equality ▸ finite_bound (index + offset) index⟩

theorem amplitude_lower (index : ℕ) : |finiteCoefficient index index| ≤ amplitude index := by
  simpa only [amplitude, Nat.add_zero] using le_ciSup (amplitude_bounded index) 0

theorem amplitude_positive (index : ℕ) : 0 < amplitude index :=
  (abs_pos.mpr (finite_nonzero index index le_rfl)).trans_le (amplitude_lower index)

theorem amplitude_bound (index : ℕ) : amplitude index ≤ coefficientBound index :=
  ciSup_le (fun offset => finite_bound (index + offset) index)

theorem coefficient_absolute (index : ℕ) : |coefficient index| = amplitude index := by
  simp only [coefficient, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (amplitude_positive index)]

theorem coefficient_sign (index : ℕ) : Real.sign (coefficient index) = (-1 : ℝ) ^ index := by
  rcases neg_one_pow_eq_or ℝ index with positive | negative
  · simp only [coefficient, positive, one_mul, Real.sign_of_pos (amplitude_positive index)]
  · simp only [coefficient, negative, neg_one_mul, Real.sign_of_neg (neg_lt_zero.mpr (amplitude_positive index))]

theorem coefficient_nonzero (index : ℕ) : coefficient index ≠ 0 := by
  apply abs_pos.mp
  rw [coefficient_absolute]
  exact amplitude_positive index

theorem coefficient_bound (index : ℕ) : |coefficient index| ≤ coefficientBound index := by
  rw [coefficient_absolute]
  exact amplitude_bound index

theorem coefficient_tendsto (index : ℕ) :
    Tendsto (fun cutoff => finiteCoefficient cutoff index) atTop (𝓝 (coefficient index)) := by
  have limit : Tendsto (fun offset => |finiteCoefficient (index + offset) index|) atTop (𝓝 (amplitude index)) :=
    tendsto_atTop_ciSup (amplitude_monotone index) (amplitude_bounded index)
  have signed := limit.const_mul ((-1 : ℝ) ^ index)
  have equality (offset : ℕ) := finite_eq_signed_absolute (index + offset) index (by omega)
  have shifted : Tendsto (fun offset => finiteCoefficient (index + offset) index) atTop (𝓝 (coefficient index)) :=
    (tendsto_congr equality).mpr signed
  apply (tendsto_add_atTop_iff_nat index).mp
  simpa only [Nat.add_comm] using shifted

theorem limit_goal : LimitGoal :=
  ⟨fun index => ⟨amplitude_monotone index, amplitude_bounded index⟩, coefficient_tendsto,
    fun index => ⟨amplitude_lower index, amplitude_positive index, amplitude_bound index⟩,
    fun index => ⟨coefficient_absolute index, coefficient_sign index, coefficient_nonzero index⟩,
    coefficient_bound⟩

end Grad.DiskExtension.Seeley
