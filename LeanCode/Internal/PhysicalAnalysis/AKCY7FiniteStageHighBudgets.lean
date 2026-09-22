import AKCY6OriginalNewtonNeighborhood
import NewtonFiniteStage

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators

namespace Grad.NashMoser.OriginalIteration
open Grad.NashMoser.Numeric

/-- The written predecessor time, including T(-1), as one total formula. -/
def previousStageTime (initial : ℝ) (index : ℕ) : ℝ :=
  newtonTime initial index ^ (2/3:ℝ)

theorem previousStageTime_positive (initial : ℝ) (positive : 0 < initial) (index : ℕ) :
    0 < previousStageTime initial index := Real.rpow_pos_of_pos (newtonTime_pos positive index) _

theorem previousStageTime_one_le (initial : ℝ) (large : 1 ≤ initial) (index : ℕ) :
    1 ≤ previousStageTime initial index :=
  Real.one_le_rpow (large.trans (newtonTime_lower large index)) (by norm_num)

theorem previousStageTime_succ (initial : ℝ) (positive : 0 < initial) (index : ℕ) :
    previousStageTime initial (index+1) = newtonTime initial index := by
  rw [previousStageTime,newtonTime_add positive,pow_one,← Real.rpow_mul (newtonTime_pos positive index).le]
  norm_num

theorem newtonTime_le_previousStageTime (initial : ℝ) (large : 1 ≤ initial)
    (stage index : ℕ) (before : stage < index) :
    newtonTime initial stage ≤ previousStageTime initial index := by
  have positive : 0 < initial := lt_of_lt_of_le zero_lt_one large
  have powers : (3/2:ℝ)^(stage+1) ≤ (3/2:ℝ)^index :=
    pow_le_pow_right₀ (by norm_num) (Nat.succ_le_iff.mpr before)
  rw [pow_succ] at powers
  unfold previousStageTime newtonTime
  rw [← Real.rpow_mul positive.le]
  apply Real.rpow_le_rpow_of_exponent_le large
  nlinarith

/-- Actual accumulated correction budget in every original grade. -/
def stageGradeBudget (initial loss constant : ℝ) (grade index : ℕ) : ℝ :=
  constant * ∑ stage ∈ Finset.range index,
    newtonTime initial stage ^ (grade:ℝ) * newtonTime initial stage ^ (-initialDecay loss)

theorem stageGradeBudget_zero (initial loss constant : ℝ) (grade : ℕ) :
    stageGradeBudget initial loss constant grade 0 = 0 := by simp [stageGradeBudget]

theorem stageGradeBudget_succ (initial loss constant : ℝ) (grade index : ℕ) :
    stageGradeBudget initial loss constant grade (index+1) =
    stageGradeBudget initial loss constant grade index +
      constant * newtonTime initial index ^ (grade:ℝ) * newtonTime initial index ^ (-initialDecay loss) := by
  simp only [stageGradeBudget,Finset.sum_range_succ,mul_add,mul_assoc]

theorem stageGradeBudget_at_loss (initial constant : ℝ) (positive : 0 < initial) (loss index : ℕ) :
    stageGradeBudget initial loss constant loss index = finiteCorrectionBudget initial loss constant index := by
  unfold stageGradeBudget finiteCorrectionBudget
  congr 1
  apply Finset.sum_congr rfl
  intro stage _
  rw [← Real.rpow_add (newtonTime_pos positive stage)]
  congr 1
  ring

theorem finiteResidualBudget_le_one (initial loss : ℝ) (initialLarge : 4 ≤ initial)
    (lossLarge : 1 ≤ loss) (index : ℕ) :
    ∑ stage ∈ Finset.range index, newtonTime initial stage ^ (-initialDecay loss) ≤ 1 := by
  have gap : 2 ≤ initialDecay loss := by unfold initialDecay; linarith
  obtain ⟨summable,tail⟩ := newtonTime_tail initialLarge gap 0
  simp only [zero_add] at summable tail
  have finiteBound := summable.sum_le_tsum (Finset.range index)
    (fun stage _ => Real.rpow_nonneg (newtonTime_pos (by linarith : 0 < initial) stage).le _)
  have smallPower : initial ^ (-initialDecay loss) ≤ (4:ℝ)^(-2:ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ initial) (by linarith : -initialDecay loss ≤ -2)).trans
      (Real.rpow_le_rpow_of_nonpos (by norm_num) initialLarge (by norm_num))
  have final : 2*initial^(-initialDecay loss) ≤ 1 := by
    have small := mul_le_mul_of_nonneg_left smallPower (by norm_num : (0:ℝ) ≤ 2)
    norm_num [Real.rpow_neg,Real.rpow_natCast] at small
    linarith
  simp only [newtonTime,pow_zero,Real.rpow_one] at tail
  exact finiteBound.trans (tail.trans final)

/-- Written NM06 coarse high bound follows from finite residual decay and
the SAME accumulated corrections. It is not assumed for arbitrary states. -/
theorem stageGradeBudget_coarse (initial loss constant : ℝ) (initialLarge : 4 ≤ initial)
    (lossLarge : 1 ≤ loss) (nonnegative : 0 ≤ constant) (grade index : ℕ) :
    stageGradeBudget initial loss constant grade index ≤
      constant * previousStageTime initial index ^ (grade:ℝ) := by
  have powers (stage : ℕ) (member : stage ∈ Finset.range index) :
      newtonTime initial stage ^ (grade:ℝ) ≤ previousStageTime initial index ^ (grade:ℝ) :=
    Real.rpow_le_rpow (newtonTime_pos (by linarith : 0 < initial) stage).le
      (newtonTime_le_previousStageTime initial (by linarith) stage index (Finset.mem_range.mp member))
      (Nat.cast_nonneg grade)
  have sumBound := Finset.sum_le_sum (s := Finset.range index) (fun stage member =>
    mul_le_mul_of_nonneg_right (powers stage member)
      (Real.rpow_nonneg (newtonTime_pos (by linarith : 0 < initial) stage).le (-initialDecay loss)))
  rw [← Finset.mul_sum] at sumBound
  have whole := mul_le_mul_of_nonneg_left sumBound nonnegative
  change stageGradeBudget initial loss constant grade index ≤ _ at whole
  exact whole.trans (by
    have bound := mul_le_mul_of_nonneg_left (finiteResidualBudget_le_one initial loss initialLarge lossLarge index)
      (mul_nonneg nonnegative (Real.rpow_nonneg (previousStageTime_positive initial (by linarith) index).le (grade:ℝ)))
    simpa only [mul_one,mul_assoc] using bound)

end Grad.NashMoser.OriginalIteration
