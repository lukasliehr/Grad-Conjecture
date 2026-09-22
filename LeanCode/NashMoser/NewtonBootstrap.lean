import NewtonTimeConsumer
import Mathlib.Algebra.Order.Floor.Semiring

noncomputable section

open Filter

namespace Grad.NashMoser.Numeric

def initialDecay (loss : ℝ) : ℝ := 8 * loss + 8

/-- The bootstrap index changes the estimate only, never the Newton times. -/
def bootstrapExponent (loss : ℝ) : ℕ → ℝ :=
  Nat.rec (initialDecay loss)
    (fun _ previous => 4 * loss + (7 / 6) * (previous - 4 * loss))

theorem bootstrapExponent_zero (loss : ℝ) :
    bootstrapExponent loss 0 = initialDecay loss := rfl

theorem bootstrapExponent_succ (loss : ℝ) (index : ℕ) :
    bootstrapExponent loss (index + 1) =
      4 * loss + (7 / 6) * (bootstrapExponent loss index - 4 * loss) := rfl

theorem bootstrapExponent_formula (loss : ℝ) (index : ℕ) :
    bootstrapExponent loss index =
      4 * loss + (initialDecay loss - 4 * loss) * (7 / 6 : ℝ) ^ index := by
  induction index with
  | zero => simp only [bootstrapExponent_zero, pow_zero, mul_one]; ring
  | succ index inductionHypothesis =>
    rw [bootstrapExponent_succ, inductionHypothesis, pow_succ]
    ring

theorem bootstrapExponent_above {loss : ℝ} (lossLarge : 1 ≤ loss) (index : ℕ) :
    4 * loss < bootstrapExponent loss index := by
  rw [bootstrapExponent_formula]
  have basePositive : 0 < initialDecay loss - 4 * loss := by
    unfold initialDecay
    linarith
  have positive : 0 < (7 / 6 : ℝ) ^ index := pow_pos (by norm_num) _
  nlinarith [mul_pos basePositive positive]

theorem bootstrapExponent_margin (loss : ℝ) (index : ℕ) :
    2 * bootstrapExponent loss index - 2 * loss -
        (3 / 2) * bootstrapExponent loss (index + 1) =
      (bootstrapExponent loss index - 4 * loss) / 4 := by
  rw [bootstrapExponent_succ]
  ring

theorem bootstrapExponent_margin_pos {loss : ℝ} (lossLarge : 1 ≤ loss)
    (index : ℕ) :
    0 < 2 * bootstrapExponent loss index - 2 * loss -
      (3 / 2) * bootstrapExponent loss (index + 1) := by
  rw [bootstrapExponent_margin]
  linarith [bootstrapExponent_above lossLarge index]

theorem bootstrapExponent_tendsto {loss : ℝ} (lossLarge : 1 ≤ loss) :
    Tendsto (bootstrapExponent loss) atTop atTop := by
  have positive : 0 < initialDecay loss - 4 * loss := by
    unfold initialDecay
    linarith
  have growth := (tendsto_pow_atTop_atTop_of_one_lt
    (by norm_num : (1 : ℝ) < 7 / 6)).const_mul_atTop positive
  apply tendsto_atTop_mono (fun index => ?_) growth
  rw [bootstrapExponent_formula]
  linarith

def bootstrapCutoff (loss : ℝ) (index : ℕ) : ℕ :=
  ⌈(9 / 2) * bootstrapExponent loss (index + 1) + 8 * loss⌉₊

theorem bootstrapCutoff_bound (loss : ℝ) (index : ℕ) :
    (3 / 2) * bootstrapExponent loss (index + 1) ≤
      ((bootstrapCutoff loss index : ℝ) - 8 * loss) / 3 := by
  have bound := Nat.le_ceil
    ((9 / 2) * bootstrapExponent loss (index + 1) + 8 * loss)
  change _ ≤ (((⌈(9 / 2) * bootstrapExponent loss (index + 1) + 8 * loss⌉₊ : ℕ) : ℝ)
    - 8 * loss) / 3
  linarith

def bootstrapConstant (initial loss quadratic : ℝ) (smoothing : ℕ → ℝ) : ℕ → ℝ :=
  Nat.rec 1 (fun index previous => max 1
      (max (initial ^ (bootstrapExponent loss (index + 1) - initialDecay loss))
        (quadratic * previous ^ 2 + smoothing (bootstrapCutoff loss index))))

theorem bootstrapConstant_one_le (initial loss quadratic : ℝ)
    (smoothing : ℕ → ℝ) (index : ℕ) :
    1 ≤ bootstrapConstant initial loss quadratic smoothing index := by
  cases index with
  | zero => rfl
  | succ index => exact le_max_left _ _

/-- Numerical bootstrap for the same residual sequence. The actual nonlinear
construction must supply both the base decay and its all-cutoff recurrence. -/
theorem same_sequence_bootstrap_decay
    (initial loss quadratic : ℝ) (smoothing residual : ℕ → ℝ)
    (initialLarge : 4 ≤ initial) (lossLarge : 1 ≤ loss)
    (quadraticNonnegative : 0 ≤ quadratic)
    (smoothingNonnegative : ∀ cutoff, 0 ≤ smoothing cutoff)
    (residualNonnegative : ∀ index, 0 ≤ residual index)
    (baseDecay : ∀ index, residual index ≤
      newtonTime initial index ^ (-initialDecay loss))
    (recurrence : ∀ index cutoff,
      residual (index + 1) ≤
        quadratic * newtonTime initial index ^ (2 * loss) * residual index ^ 2 +
        smoothing cutoff * newtonTime initial index ^
          (-(((cutoff : ℝ) - 8 * loss) / 3))) :
    ∀ order index, residual index ≤
      bootstrapConstant initial loss quadratic smoothing order *
        newtonTime initial index ^ (-bootstrapExponent loss order) := by
  have initialPositive : 0 < initial := by linarith
  intro order
  induction order with
  | zero =>
    change ∀ index, residual index ≤ 1 * newtonTime initial index ^ (-initialDecay loss)
    simpa only [one_mul] using baseDecay
  | succ order inductionHypothesis =>
    intro index
    let nextPower := bootstrapExponent loss (order + 1)
    let previousPower := bootstrapExponent loss order
    let previousConstant := bootstrapConstant initial loss quadratic smoothing order
    let nextConstant := bootstrapConstant initial loss quadratic smoothing (order + 1)
    have nextInitialBound : initial ^ (nextPower - initialDecay loss) ≤ nextConstant :=
      (le_max_left _ _).trans (le_max_right _ _)
    have nextStepBound : quadratic * previousConstant ^ 2 +
        smoothing (bootstrapCutoff loss order) ≤ nextConstant :=
      (le_max_right _ _).trans (le_max_right _ _)
    cases index with
    | zero =>
      have bound := mul_le_mul_of_nonneg_right nextInitialBound
        (Real.rpow_nonneg initialPositive.le (-nextPower))
      have identity : initial ^ (nextPower - initialDecay loss) *
          initial ^ (-nextPower) = initial ^ (-initialDecay loss) := by
        rw [← Real.rpow_add initialPositive]
        congr 1
        ring
      rw [identity] at bound
      have initialBound : residual 0 ≤ initial ^ (-initialDecay loss) := by
        simpa only [newtonTime, pow_zero, Real.rpow_one] using baseDecay 0
      simpa only [newtonTime, pow_zero, Real.rpow_one] using initialBound.trans bound
    | succ index =>
      let time := newtonTime initial index
      have timePositive : 0 < time := newtonTime_pos initialPositive index
      have timeLarge : 1 ≤ time :=
        (by linarith : 1 ≤ initial).trans
          (newtonTime_lower (by linarith) index)
      have squareBound : residual index ^ 2 ≤
          (previousConstant * time ^ (-previousPower)) ^ 2 := by
        have nonnegative := residualNonnegative index
        have bound := inductionHypothesis index
        change residual index ≤ previousConstant * time ^ (-previousPower) at bound
        nlinarith
      have margin : 2 * loss - 2 * previousPower ≤ -(3 / 2) * nextPower := by
        have := bootstrapExponent_margin_pos lossLarge order
        change 0 < 2 * previousPower - 2 * loss - (3 / 2) * nextPower at this
        linarith
      have quadraticBound :
          quadratic * time ^ (2 * loss) * residual index ^ 2 ≤
            (quadratic * previousConstant ^ 2) * time ^ (-(3 / 2) * nextPower) := by
        calc
          _ ≤ quadratic * time ^ (2 * loss) *
              (previousConstant * time ^ (-previousPower)) ^ 2 :=
            mul_le_mul_of_nonneg_left squareBound
              (mul_nonneg quadraticNonnegative (Real.rpow_nonneg timePositive.le _))
          _ = (quadratic * previousConstant ^ 2) *
              time ^ (2 * loss - 2 * previousPower) := by
            rw [mul_pow, ← Real.rpow_natCast (time ^ (-previousPower)) 2,
              ← Real.rpow_mul timePositive.le]
            norm_num only [Nat.cast_ofNat]
            rw [show (-previousPower) * (2 : ℝ) = -2 * previousPower by ring]
            rw [show 2 * loss - 2 * previousPower =
              2 * loss + -2 * previousPower by ring, Real.rpow_add timePositive]
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le timeLarge margin)
            (mul_nonneg quadraticNonnegative (sq_nonneg _))
      have smoothingBound :
          smoothing (bootstrapCutoff loss order) *
              time ^ (-(((bootstrapCutoff loss order : ℝ) - 8 * loss) / 3)) ≤
            smoothing (bootstrapCutoff loss order) * time ^ (-(3 / 2) * nextPower) := by
        apply mul_le_mul_of_nonneg_left _ (smoothingNonnegative _)
        apply Real.rpow_le_rpow_of_exponent_le timeLarge
        have := bootstrapCutoff_bound loss order
        change (3 / 2) * nextPower ≤ _ at this
        linarith
      have powerIdentity : time ^ (-(3 / 2) * nextPower) =
          newtonTime initial (index + 1) ^ (-nextPower) := by
        rw [newtonTime_add initialPositive, pow_one, ← Real.rpow_mul timePositive.le]
        congr 1
        ring
      calc
        residual (index + 1) ≤ _ := recurrence index (bootstrapCutoff loss order)
        _ ≤ (quadratic * previousConstant ^ 2 + smoothing (bootstrapCutoff loss order)) *
            time ^ (-(3 / 2) * nextPower) := by
          rw [add_mul]
          exact add_le_add quadraticBound smoothingBound
        _ ≤ nextConstant * time ^ (-(3 / 2) * nextPower) :=
          mul_le_mul_of_nonneg_right nextStepBound (Real.rpow_nonneg timePositive.le _)
        _ = _ := by rw [powerIdentity]

end Grad.NashMoser.Numeric
