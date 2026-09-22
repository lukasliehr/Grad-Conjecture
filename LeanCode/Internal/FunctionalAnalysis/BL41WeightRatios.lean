import BL40HighSupport
import AW1Submultiplicative

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

theorem boundaryPhase_eq_spectralPhase (parameters : PhaseParameters) (cell : ℤ) :
    boundaryPhase parameters cell =
      Grad.AnalyticWeights.spectralPhase parameters.sigma0 parameters.gamma 1 (cellFrequency cell) := by
  unfold boundaryPhase Grad.AnalyticWeights.spectralPhase
  rw [one_pow, one_mul]

theorem cellFrequency_sub_le (n k : ℤ) :
    cellFrequency n ≤ cellFrequency (n - k) + cellFrequency k := by
  have law := Grad.AnalyticWeights.cellWeight_add_le (n - k) k
  rw [sub_add_cancel] at law
  exact law

/-- The exact N28 cell phase increment: shifting the cell index costs at
most the literal seed exponential of the shift frequency. -/
theorem boundaryPhase_shift_le (parameters : PhaseParameters) (n k : ℤ) :
    boundaryPhase parameters n ≤
      parameters.sigma0 * cellFrequency k + boundaryPhase parameters (n - k) := by
  have sigmaPos : 0 < parameters.sigma0 :=
    parameters.gamma_pos.trans (parameters_gamma_lt_sigma0 parameters)
  have frequencyPos := cellFrequency_pos k
  rcases le_total (cellFrequency n) (cellFrequency (n - k)) with ordered | ordered
  · have rateNonneg : 0 ≤ Grad.AnalyticWeights.rate parameters.sigma0 parameters.gamma 1 := by
      unfold Grad.AnalyticWeights.rate
      rw [mul_one]
      linarith [parameters_gamma_lt_sigma0 parameters]
    have monotone := Grad.AnalyticWeights.spectralPhase_mono parameters.sigma0 parameters.gamma 1
      (cellFrequency n) (cellFrequency (n - k)) parameters.gamma_pos.le zero_le_one rateNonneg
      (cellFrequency_pos n).le ordered
    rw [← boundaryPhase_eq_spectralPhase, ← boundaryPhase_eq_spectralPhase] at monotone
    nlinarith
  · have rootMono : Real.sqrt (1 + cellFrequency (n - k) ^ 2) ≤
        Real.sqrt (1 + cellFrequency n ^ 2) := by
      apply Real.sqrt_le_sqrt
      nlinarith [cellFrequency_pos (n - k), cellFrequency_pos n]
    have gammaRoot : parameters.gamma * (Real.sqrt (1 + cellFrequency (n - k) ^ 2) - 1) ≤
        parameters.gamma * (Real.sqrt (1 + cellFrequency n ^ 2) - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) parameters.gamma_pos.le
    have sigmaSplit : parameters.sigma0 * cellFrequency n ≤
        parameters.sigma0 * cellFrequency (n - k) + parameters.sigma0 * cellFrequency k := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (cellFrequency_sub_le n k) sigmaPos.le
    unfold boundaryPhase
    linarith

theorem boundaryFrequency_shift_triangle_snd (m n k : ℤ) :
    boundaryFrequency (m, n) ≤ boundaryFrequency (m, n - k) + |(k : ℝ)| := by
  have absLe : |(n : ℝ) - (k : ℝ)| ≤ boundaryFrequency (m, n - k) := by
    rw [show |(n : ℝ) - (k : ℝ)| = Real.sqrt (((n : ℝ) - (k : ℝ)) ^ 2) from
      (Real.sqrt_sq_eq_abs _).symm]
    simp only [boundaryFrequency]
    apply Real.sqrt_le_sqrt
    push_cast
    nlinarith [sq_nonneg (m : ℝ)]
  have expand : boundaryFrequency (m, n - k) ^ 2 = 1 + (m : ℝ) ^ 2 + ((n : ℝ) - (k : ℝ)) ^ 2 := by
    rw [boundaryFrequency_sq]
    push_cast
    ring
  have target : (1 : ℝ) + (m : ℝ) ^ 2 + (n : ℝ) ^ 2 ≤
      (boundaryFrequency (m, n - k) + |(k : ℝ)|) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right absLe (abs_nonneg (k : ℝ)), sq_abs (k : ℝ),
      le_abs_self (((n : ℝ) - (k : ℝ)) * (k : ℝ)), abs_mul ((n : ℝ) - (k : ℝ)) (k : ℝ)]
  calc boundaryFrequency (m, n) = Real.sqrt (1 + (m : ℝ) ^ 2 + (n : ℝ) ^ 2) := rfl
    _ ≤ Real.sqrt ((boundaryFrequency (m, n - k) + |(k : ℝ)|) ^ 2) := Real.sqrt_le_sqrt target
    _ = boundaryFrequency (m, n - k) + |(k : ℝ)| :=
        Real.sqrt_sq (add_nonneg (boundaryFrequency_pos _).le (abs_nonneg _))

theorem boundaryFrequency_shift_triangle_fst (m n s : ℤ) :
    boundaryFrequency (m, n) ≤ boundaryFrequency (m - s, n) + |(s : ℝ)| := by
  have absLe : |(m : ℝ) - (s : ℝ)| ≤ boundaryFrequency (m - s, n) := by
    rw [show |(m : ℝ) - (s : ℝ)| = Real.sqrt (((m : ℝ) - (s : ℝ)) ^ 2) from
      (Real.sqrt_sq_eq_abs _).symm]
    simp only [boundaryFrequency]
    apply Real.sqrt_le_sqrt
    push_cast
    nlinarith [sq_nonneg (n : ℝ)]
  have target : (1 : ℝ) + (m : ℝ) ^ 2 + (n : ℝ) ^ 2 ≤
      (boundaryFrequency (m - s, n) + |(s : ℝ)|) ^ 2 := by
    have expand : boundaryFrequency (m - s, n) ^ 2 = 1 + ((m : ℝ) - (s : ℝ)) ^ 2 + (n : ℝ) ^ 2 := by
      rw [boundaryFrequency_sq]
      push_cast
      ring
    nlinarith [mul_le_mul_of_nonneg_right absLe (abs_nonneg (s : ℝ)), sq_abs (s : ℝ),
      le_abs_self (((m : ℝ) - (s : ℝ)) * (s : ℝ)), abs_mul ((m : ℝ) - (s : ℝ)) (s : ℝ)]
  calc boundaryFrequency (m, n) = Real.sqrt (1 + (m : ℝ) ^ 2 + (n : ℝ) ^ 2) := rfl
    _ ≤ Real.sqrt ((boundaryFrequency (m - s, n) + |(s : ℝ)|) ^ 2) := Real.sqrt_le_sqrt target
    _ = boundaryFrequency (m - s, n) + |(s : ℝ)| :=
        Real.sqrt_sq (add_nonneg (boundaryFrequency_pos _).le (abs_nonneg _))

theorem boundaryFrequency_cell_shift_le (m n k : ℤ) :
    boundaryFrequency (m, n) ≤ cellPolynomialWeight k * boundaryFrequency (m, n - k) := by
  have triangle := boundaryFrequency_shift_triangle_snd m n k
  have oneLe := boundaryFrequency_one_le (m, n - k)
  rw [cellPolynomialWeight_formula]
  nlinarith [abs_nonneg (k : ℝ)]

theorem boundaryFrequency_angular_shift_le (m n s : ℤ) :
    boundaryFrequency (m, n) ≤ cellPolynomialWeight s * boundaryFrequency (m - s, n) := by
  have triangle := boundaryFrequency_shift_triangle_fst m n s
  have oneLe := boundaryFrequency_one_le (m - s, n)
  rw [cellPolynomialWeight_formula]
  nlinarith [abs_nonneg (s : ℝ)]

/-- The half-order polynomial ratio costs at most the whole-power
polynomial weight of the shift. -/
theorem sqrt_pow_ratio_le (grade : ℕ) (ratio first second : ℝ) (oneLeRatio : 1 ≤ ratio)
    (firstNonneg : 0 ≤ first) (comparison : first ≤ ratio * second) :
    Real.sqrt (first ^ (2 * grade - 1)) ≤
      ratio ^ grade * Real.sqrt (second ^ (2 * grade - 1)) := by
  have ratioNonneg : (0 : ℝ) ≤ ratio := zero_le_one.trans oneLeRatio
  have powerBound : first ^ (2 * grade - 1) ≤ (ratio * second) ^ (2 * grade - 1) :=
    pow_le_pow_left₀ firstNonneg comparison _
  have ratioPower : Real.sqrt (ratio ^ (2 * grade - 1)) ≤ ratio ^ grade := by
    have exponent : ratio ^ (2 * grade - 1) ≤ ratio ^ (grade * 2) :=
      pow_le_pow_right₀ oneLeRatio (by omega)
    calc Real.sqrt (ratio ^ (2 * grade - 1)) ≤ Real.sqrt (ratio ^ (grade * 2)) :=
          Real.sqrt_le_sqrt exponent
      _ = ratio ^ grade := by
          rw [pow_mul, Real.sqrt_sq (pow_nonneg ratioNonneg grade)]
  calc Real.sqrt (first ^ (2 * grade - 1)) ≤ Real.sqrt ((ratio * second) ^ (2 * grade - 1)) :=
        Real.sqrt_le_sqrt powerBound
    _ = Real.sqrt (ratio ^ (2 * grade - 1)) * Real.sqrt (second ^ (2 * grade - 1)) := by
        rw [mul_pow, Real.sqrt_mul (pow_nonneg ratioNonneg _)]
    _ ≤ ratio ^ grade * Real.sqrt (second ^ (2 * grade - 1)) :=
        mul_le_mul_of_nonneg_right ratioPower (Real.sqrt_nonneg _)

/-- The literal N28 boundary weight envelope for one cell shift. -/
theorem boundaryWeight_cell_shift_le (parameters : PhaseParameters) (grade : ℕ) (m n k : ℤ) :
    boundaryWeight parameters grade (m, n) ≤
      Real.exp (parameters.sigma0 * cellFrequency k) * cellPolynomialWeight k ^ grade *
        boundaryWeight parameters grade (m, n - k) := by
  have phaseBound : Real.exp (boundaryPhase parameters n) ≤
      Real.exp (parameters.sigma0 * cellFrequency k) * Real.exp (boundaryPhase parameters (n - k)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (boundaryPhase_shift_le parameters n k)
  have sqrtBound : Real.sqrt (boundaryFrequency (m, n) ^ (2 * grade - 1)) ≤
      cellPolynomialWeight k ^ grade * Real.sqrt (boundaryFrequency (m, n - k) ^ (2 * grade - 1)) :=
    sqrt_pow_ratio_le grade (cellPolynomialWeight k) (boundaryFrequency (m, n))
      (boundaryFrequency (m, n - k)) (cellPolynomialWeight_one_le k)
      (boundaryFrequency_pos _).le (boundaryFrequency_cell_shift_le m n k)
  simp only [boundaryWeight]
  calc Real.exp (boundaryPhase parameters n) * Real.sqrt (boundaryFrequency (m, n) ^ (2 * grade - 1))
      ≤ (Real.exp (parameters.sigma0 * cellFrequency k) * Real.exp (boundaryPhase parameters (n - k))) *
          (cellPolynomialWeight k ^ grade * Real.sqrt (boundaryFrequency (m, n - k) ^ (2 * grade - 1))) :=
        mul_le_mul phaseBound sqrtBound (Real.sqrt_nonneg _) (by positivity)
    _ = Real.exp (parameters.sigma0 * cellFrequency k) * cellPolynomialWeight k ^ grade *
          (Real.exp (boundaryPhase parameters (n - k)) *
            Real.sqrt (boundaryFrequency (m, n - k) ^ (2 * grade - 1))) := by ring

/-- The literal angular shift weight envelope: the phase is untouched and
only the polynomial half-order ratio appears. -/
theorem boundaryWeight_angular_shift_le (parameters : PhaseParameters) (grade : ℕ) (m n s : ℤ) :
    boundaryWeight parameters grade (m, n) ≤
      cellPolynomialWeight s ^ grade * boundaryWeight parameters grade (m - s, n) := by
  have sqrtBound : Real.sqrt (boundaryFrequency (m, n) ^ (2 * grade - 1)) ≤
      cellPolynomialWeight s ^ grade * Real.sqrt (boundaryFrequency (m - s, n) ^ (2 * grade - 1)) :=
    sqrt_pow_ratio_le grade (cellPolynomialWeight s) (boundaryFrequency (m, n))
      (boundaryFrequency (m - s, n)) (cellPolynomialWeight_one_le s)
      (boundaryFrequency_pos _).le (boundaryFrequency_angular_shift_le m n s)
  simp only [boundaryWeight]
  calc Real.exp (boundaryPhase parameters n) * Real.sqrt (boundaryFrequency (m, n) ^ (2 * grade - 1))
      ≤ Real.exp (boundaryPhase parameters n) *
          (cellPolynomialWeight s ^ grade * Real.sqrt (boundaryFrequency (m - s, n) ^ (2 * grade - 1))) :=
        mul_le_mul_of_nonneg_left sqrtBound (Real.exp_pos _).le
    _ = cellPolynomialWeight s ^ grade *
          (Real.exp (boundaryPhase parameters n) *
            Real.sqrt (boundaryFrequency (m - s, n) ^ (2 * grade - 1))) := by ring

end Grad.BoundaryLift
