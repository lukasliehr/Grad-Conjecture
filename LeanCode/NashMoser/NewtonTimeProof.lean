import NewtonTimeInterface
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section

namespace Grad.NashMoser.Numeric

theorem newtonTime_pos {initial : ℝ} (positive : 0 < initial) (index : ℕ) :
    0 < newtonTime initial index :=
  Real.rpow_pos_of_pos positive _

theorem newtonTime_lower {initial : ℝ} (large : 1 ≤ initial) (index : ℕ) :
    initial ≤ newtonTime initial index := by
  unfold newtonTime
  exact Real.self_le_rpow_of_one_le large (one_le_pow₀ (by norm_num))

theorem newtonTime_add {initial : ℝ} (positive : 0 < initial)
    (index offset : ℕ) :
    newtonTime initial (index + offset) =
      newtonTime initial index ^ ((3 / 2 : ℝ) ^ offset) := by
  unfold newtonTime
  rw [pow_add, Real.rpow_mul positive.le]

theorem newtonExponent_lower (offset : ℕ) :
    1 + (offset : ℝ) / 2 ≤ (3 / 2 : ℝ) ^ offset := by
  induction offset with
  | zero => norm_num
  | succ offset inductionHypothesis =>
    rw [pow_succ, Nat.cast_succ]
    have nonnegative : (0 : ℝ) ≤ offset := Nat.cast_nonneg _
    nlinarith

theorem newtonTime_growth {initial : ℝ} (large : 4 ≤ initial)
    (index offset : ℕ) :
    newtonTime initial index ^ (1 + (offset : ℝ) / 2) ≤
      newtonTime initial (index + offset) := by
  rw [newtonTime_add (by linarith : 0 < initial)]
  exact Real.rpow_le_rpow_of_exponent_le
    (le_trans (by linarith : 1 ≤ initial)
      (newtonTime_lower (by linarith) index)) (newtonExponent_lower offset)

theorem newtonTime_geometric_majorant {initial exponent : ℝ}
    (large : 4 ≤ initial) (exponentLarge : 2 ≤ exponent)
    (index offset : ℕ) :
    newtonTime initial (index + offset) ^ (-exponent) ≤
      newtonTime initial index ^ (-exponent) *
        (newtonTime initial index ^ (-exponent / 2)) ^ offset := by
  have positive := newtonTime_pos (by linarith : 0 < initial) index
  calc
    _ ≤ (newtonTime initial index ^ (1 + (offset : ℝ) / 2)) ^
        (-exponent) := Real.rpow_le_rpow_of_nonpos
      (Real.rpow_pos_of_pos positive _) (newtonTime_growth large index offset)
      (by linarith)
    _ = _ := by
      rw [← Real.rpow_mul positive.le,
        show (1 + (offset : ℝ) / 2) * -exponent =
          -exponent + (-exponent / 2) * (offset : ℝ) by ring,
        Real.rpow_add positive, Real.rpow_mul_natCast positive.le]

theorem newtonTime_ratio_le {initial exponent : ℝ}
    (large : 4 ≤ initial) (exponentLarge : 2 ≤ exponent) (index : ℕ) :
    newtonTime initial index ^ (-exponent / 2) ≤ 1 / 2 := by
  have timeLarge : 4 ≤ newtonTime initial index :=
    large.trans (newtonTime_lower (by linarith) index)
  calc
    _ ≤ newtonTime initial index ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ ≤ (4 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) timeLarge (by norm_num)
    _ ≤ 1 / 2 := by norm_num

theorem newtonTime_tail {initial exponent : ℝ}
    (large : 4 ≤ initial) (exponentLarge : 2 ≤ exponent) (index : ℕ) :
    Summable (fun offset : ℕ =>
      newtonTime initial (index + offset) ^ (-exponent)) ∧
    (∑' offset : ℕ, newtonTime initial (index + offset) ^ (-exponent)) ≤
      2 * newtonTime initial index ^ (-exponent) := by
  let ratio := newtonTime initial index ^ (-exponent / 2)
  have ratioNonnegative : 0 ≤ ratio := Real.rpow_nonneg
    (newtonTime_pos (by linarith) index).le _
  have ratioBound : ratio ≤ 1 / 2 := newtonTime_ratio_le large exponentLarge index
  have ratioSmall : ratio < 1 := by linarith
  have majorantSummable :=
    (summable_geometric_of_lt_one ratioNonnegative ratioSmall).mul_left
      (newtonTime initial index ^ (-exponent))
  have tailSummable : Summable (fun offset : ℕ =>
      newtonTime initial (index + offset) ^ (-exponent)) :=
    Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg
      (newtonTime_pos (by linarith) _).le _)
      (newtonTime_geometric_majorant large exponentLarge index) majorantSummable
  refine ⟨tailSummable, ?_⟩
  calc
    _ ≤ ∑' offset : ℕ,
        newtonTime initial index ^ (-exponent) * ratio ^ offset :=
      Summable.tsum_le_tsum
        (newtonTime_geometric_majorant large exponentLarge index)
        tailSummable majorantSummable
    _ = newtonTime initial index ^ (-exponent) * (1 - ratio)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one ratioNonnegative ratioSmall]
    _ ≤ 2 * newtonTime initial index ^ (-exponent) := by
      have inverseBound : (1 - ratio)⁻¹ ≤ (2 : ℝ) := by
        rw [← one_div]
        apply (div_le_iff₀ (by linarith : 0 < 1 - ratio)).2
        linarith
      have := mul_le_mul_of_nonneg_left inverseBound
        (Real.rpow_nonneg
          (newtonTime_pos (by linarith : 0 < initial) index).le (-exponent))
      simpa only [mul_comm] using this

theorem newton_time_and_tail_sum : NewtonTimeGoal := by
  intro initial large
  exact ⟨newtonTime_growth large, fun index _ exponentLarge =>
    newtonTime_tail large exponentLarge index⟩

end Grad.NashMoser.Numeric
