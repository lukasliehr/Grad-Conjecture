import CB1Interface
import Mathlib.Data.Nat.Choose.Sum

noncomputable section

open scoped BigOperators
open Grad.CellWeights

namespace Grad.CellBinomial

theorem cellWeight_sq (cell : ℤ) : cellWeight cell ^ 2 = 1 + (cell : ℝ) ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem cellWeight_even (weight : ℕ) (cell : ℤ) :
    cellWeight cell ^ (2 * weight) = (1 + (cell : ℝ) ^ 2) ^ weight := by
  rw [pow_mul, cellWeight_sq]

theorem positiveFactor_norm (weight : ℕ) (cell : ℤ) :
    ‖positiveFactor weight cell‖ = cellWeight cell ^ weight := by
  simp only [positiveFactor, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (cellWeight_pos cell)]

theorem derivativeFactor_norm (power : ℕ) (cell : ℤ) :
    ‖derivativeFactor power cell‖ = |(cell : ℝ)| ^ power := by
  simp only [derivativeFactor, norm_pow, norm_mul, Complex.norm_I, one_mul]
  norm_cast

theorem positiveFactor_norm_sq (weight : ℕ) (cell : ℤ) :
    ‖positiveFactor weight cell‖ ^ 2 = (1 + (cell : ℝ) ^ 2) ^ weight := by
  rw [positiveFactor_norm, ← pow_mul, Nat.mul_comm, cellWeight_even]

theorem derivativeFactor_norm_sq (power : ℕ) (cell : ℤ) :
    ‖derivativeFactor power cell‖ ^ 2 = ((cell : ℝ) ^ 2) ^ power := by
  rw [derivativeFactor_norm, ← pow_mul, Nat.mul_comm, pow_mul, sq_abs]

theorem scalar_binomial (weight : ℕ) (cell : ℤ) :
    ‖positiveFactor weight cell‖ ^ 2 =
      ∑ power : Fin (weight + 1), (weight.choose power.val : ℝ) *
        ‖derivativeFactor power.val cell‖ ^ 2 := by
  simp only [positiveFactor_norm_sq, derivativeFactor_norm_sq]
  rw [add_comm (1 : ℝ), add_pow, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro power _membership
  simp only [one_pow, mul_one, mul_comm]

theorem derivativeFactor_le_positive (weight power : ℕ) (bound : power ≤ weight) (cell : ℤ) :
    ‖derivativeFactor power cell‖ ≤ cellWeight cell ^ weight := by
  rw [derivativeFactor_norm]
  have cellBound : |(cell : ℝ)| ≤ cellWeight cell := by
    apply (sq_le_sq₀ (abs_nonneg _) (cellWeight_pos cell).le).mp
    rw [sq_abs, cellWeight_sq]
    linarith
  exact (pow_le_pow_left₀ (abs_nonneg _) cellBound power).trans
    (pow_le_pow_right₀ (cellWeight_one_le cell) bound)

theorem derivativeRatio_norm_le (weight power : ℕ) (bound : power ≤ weight) (cell : ℤ) :
    ‖derivativeRatio weight power cell‖ ≤ 1 := by
  rw [derivativeRatio, norm_mul, inverseFactor, norm_inv, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (cellWeight_pos cell)]
  exact (mul_le_mul_of_nonneg_right (derivativeFactor_le_positive weight power bound cell)
    (inv_nonneg.mpr (pow_nonneg (cellWeight_pos cell).le _))).trans_eq
      (mul_inv_cancel₀ (pow_ne_zero _ (cellWeight_pos cell).ne'))

theorem derivativeRatio_positive (weight power : ℕ) (cell : ℤ) :
    derivativeRatio weight power cell * positiveFactor weight cell = derivativeFactor power cell := by
  rw [derivativeRatio, mul_assoc, Grad.WeightedJets.Realization.inverse_positiveFactor, mul_one]

theorem inverseFactor_star (weight : ℕ) (cell : ℤ) :
    star (inverseFactor weight cell) = inverseFactor weight cell := by
  simp [inverseFactor]

theorem positiveFactor_star (weight : ℕ) (cell : ℤ) :
    star (positiveFactor weight cell) = positiveFactor weight cell := by
  simp [positiveFactor]

theorem synthesis_identity (weight : ℕ) (cell : ℤ) :
    (∑ power : Fin (weight + 1), (weight.choose power.val : ℂ) *
      star (derivativeRatio weight power.val cell) * derivativeFactor power.val cell) =
        positiveFactor weight cell := by
  have castSum := congrArg (fun value : ℝ => (value : ℂ)) (scalar_binomial weight cell)
  push_cast at castSum
  have scalarNorm (value : ℂ) : (‖value‖ : ℂ) ^ 2 = star value * value := by
    change (‖value‖ : ℂ) ^ 2 = (starRingEnd ℂ) value * value
    simpa only [Complex.normSq_eq_norm_sq, Complex.ofReal_pow] using
      (Complex.normSq_eq_conj_mul_self (z := value))
  simp only [scalarNorm] at castSum
  calc
    _ = (∑ power : Fin (weight + 1), (weight.choose power.val : ℂ) *
          (star (derivativeFactor power.val cell) * derivativeFactor power.val cell)) *
            inverseFactor weight cell := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro power _membership
      simp only [derivativeRatio, star_mul, inverseFactor_star]
      ring
    _ = (star (positiveFactor weight cell) * positiveFactor weight cell) *
          inverseFactor weight cell := by rw [← castSum]
    _ = positiveFactor weight cell := by
      rw [positiveFactor_star]
      have inverse := Grad.WeightedJets.Realization.inverse_positiveFactor weight cell
      calc
        _ = positiveFactor weight cell * (inverseFactor weight cell * positiveFactor weight cell) := by ring
        _ = _ := by rw [inverse, mul_one]

theorem scalar : ScalarGoal := fun weight cell =>
  ⟨cellWeight_even weight cell, scalar_binomial weight cell,
    fun power => derivativeFactor_norm power cell,
    fun power bound => derivativeRatio_norm_le weight power bound cell,
    synthesis_identity weight cell⟩

end Grad.CellBinomial
