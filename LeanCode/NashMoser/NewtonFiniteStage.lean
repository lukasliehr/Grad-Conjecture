import NewtonConvergence

noncomputable section

open scoped BigOperators

namespace Grad.NashMoser.Numeric

/-- The one cutoff used to establish initial decay, fixed before iteration. -/
def initialCutoff (loss : ℕ) : ℕ := 44 * loss + 42

theorem initialCutoff_exponent (loss : ℕ) :
    ((initialCutoff loss : ℝ) - 8 * loss) / 3 =
      (3 / 2) * initialDecay loss + 2 := by
  simp only [initialCutoff, initialDecay, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem initialDecay_margin (loss : ℝ) :
    2 * initialDecay loss - 2 * loss - (3 / 2) * initialDecay loss =
      2 * loss + 4 := by
  unfold initialDecay
  ring

/-- The literal finite-cutoff recurrence closes the next residual estimate.
Only the already established current residual is used. -/
theorem next_residual_decay
    (initial quadratic smoothing residual nextResidual : ℝ) (loss index : ℕ)
    (initialLarge : 4 ≤ initial) (quadraticNonnegative : 0 ≤ quadratic)
    (smoothingNonnegative : 0 ≤ smoothing) (residualNonnegative : 0 ≤ residual)
    (quadraticSmall : quadratic * initial ^ (-(2 * (loss : ℝ) + 4)) ≤ 1 / 2)
    (smoothingSmall : smoothing * initial ^ (-2 : ℝ) ≤ 1 / 2)
    (currentDecay : residual ≤ newtonTime initial index ^ (-initialDecay loss))
    (recurrence : nextResidual ≤
      quadratic * newtonTime initial index ^ (2 * (loss : ℝ)) * residual ^ 2 +
        smoothing * newtonTime initial index ^
          (-(((initialCutoff loss : ℝ) - 8 * loss) / 3))) :
    nextResidual ≤ newtonTime initial (index + 1) ^ (-initialDecay loss) := by
  let time := newtonTime initial index
  let decay := initialDecay (loss : ℝ)
  let margin := 2 * (loss : ℝ) + 4
  have initialPositive : 0 < initial := by linarith
  have timePositive : 0 < time := newtonTime_pos initialPositive index
  have timeLower : initial ≤ time := newtonTime_lower (by linarith) index
  have marginNonnegative : 0 ≤ margin := by dsimp [margin]; positivity
  have quadraticBound : quadratic * time ^ (-margin) ≤ 1 / 2 := by
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos initialPositive timeLower (neg_nonpos.mpr marginNonnegative))
      quadraticNonnegative).trans quadraticSmall
  have smoothingBound : smoothing * time ^ (-2 : ℝ) ≤ 1 / 2 := by
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos initialPositive timeLower (by norm_num))
      smoothingNonnegative).trans smoothingSmall
  have squareBound : residual ^ 2 ≤ (time ^ (-decay)) ^ 2 := by
    change residual ≤ time ^ (-decay) at currentDecay
    nlinarith
  have factorIdentity :
      quadratic * time ^ (2 * (loss : ℝ)) * (time ^ (-decay)) ^ 2 +
        smoothing * time ^ (-(((initialCutoff loss : ℝ) - 8 * loss) / 3)) =
      (quadratic * time ^ (-margin) + smoothing * time ^ (-2 : ℝ)) *
        time ^ (-(3 / 2) * decay) := by
    rw [initialCutoff_exponent, ← Real.rpow_natCast (time ^ (-decay)) 2,
      ← Real.rpow_mul timePositive.le]
    norm_num only [Nat.cast_ofNat]
    rw [add_mul, mul_assoc quadratic, ← Real.rpow_add timePositive,
      mul_assoc quadratic, ← Real.rpow_add timePositive,
      mul_assoc smoothing, ← Real.rpow_add timePositive]
    congr 2
    · dsimp [decay, margin, initialDecay]
      ring
    · dsimp [decay]
      congr 1
      ring
  calc
    nextResidual ≤ _ := recurrence
    _ ≤ quadratic * time ^ (2 * (loss : ℝ)) * (time ^ (-decay)) ^ 2 +
        smoothing * time ^ (-(((initialCutoff loss : ℝ) - 8 * loss) / 3)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left squareBound
        (mul_nonneg quadraticNonnegative (Real.rpow_nonneg timePositive.le _))) le_rfl
    _ = _ := factorIdentity
    _ ≤ 1 * time ^ (-(3 / 2) * decay) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg timePositive.le _)
      linarith
    _ = _ := by
      rw [one_mul, newtonTime_add initialPositive, pow_one,
        ← Real.rpow_mul timePositive.le]
      congr 1
      ring

/-- Finite correction budget, computed before any next-state evaluation. -/
def finiteCorrectionBudget (initial loss highConstant : ℝ) (index : ℕ) : ℝ :=
  highConstant * ∑ stage ∈ Finset.range index,
    newtonTime initial stage ^ (-(initialDecay loss - loss))

theorem finiteCorrectionBudget_succ (initial loss highConstant : ℝ) (index : ℕ) :
    finiteCorrectionBudget initial loss highConstant (index + 1) =
      finiteCorrectionBudget initial loss highConstant index +
        highConstant * newtonTime initial index ^ (-(initialDecay loss - loss)) := by
  simp only [finiteCorrectionBudget, Finset.sum_range_succ, mul_add]

theorem finiteCorrectionBudget_le
    (initial loss highConstant : ℝ) (index : ℕ)
    (initialLarge : 4 ≤ initial) (lossLarge : 1 ≤ loss)
    (highNonnegative : 0 ≤ highConstant) :
    finiteCorrectionBudget initial loss highConstant index ≤
      2 * highConstant * initial ^ (-(initialDecay loss - loss)) := by
  have gapLarge : 2 ≤ initialDecay loss - loss := by
    unfold initialDecay
    linarith
  obtain ⟨summable, tail⟩ := newtonTime_tail initialLarge gapLarge 0
  simp only [zero_add] at summable tail
  have finiteBound := summable.sum_le_tsum (Finset.range index)
    (fun stage _ => Real.rpow_nonneg
      (newtonTime_pos (by linarith : 0 < initial) stage).le _)
  have bound := mul_le_mul_of_nonneg_left (finiteBound.trans tail) highNonnegative
  simpa only [finiteCorrectionBudget, newtonTime, pow_zero, Real.rpow_one,
    mul_left_comm highConstant 2, ← mul_assoc] using bound

end Grad.NashMoser.Numeric
