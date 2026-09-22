import GaugeTransferConsumer

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.AxisCore

open Grad.ClosedJets Grad.CartesianState

/-- The literal M16 axis weight `exp(sigma0 lambda_n) lambda_n^q`. -/
def axisWeight (parameters : PhaseParameters) (grade : ℕ) (cell : ℤ) : ℝ :=
  Real.exp (parameters.sigma0 * cellFrequency cell) * cellFrequency cell ^ grade

theorem axisWeight_pos (parameters : PhaseParameters) (grade : ℕ) (cell : ℤ) :
    0 < axisWeight parameters grade cell :=
  mul_pos (Real.exp_pos _)
    (pow_pos (lt_of_lt_of_le zero_lt_one (cellFrequency_one_le cell)) _)

theorem axisWeight_one_le (parameters : PhaseParameters) (grade : ℕ) (cell : ℤ) :
    1 ≤ axisWeight parameters grade cell := by
  unfold axisWeight
  have frequencyOne := cellFrequency_one_le cell
  have expOne : (1 : ℝ) ≤ Real.exp (parameters.sigma0 * cellFrequency cell) :=
    Real.one_le_exp (mul_nonneg parameters.sigma0_pos.le
      (lt_of_lt_of_le zero_lt_one frequencyOne).le)
  have powOne : (1 : ℝ) ≤ cellFrequency cell ^ grade := one_le_pow₀ frequencyOne
  nlinarith

theorem axisWeight_grade_le (parameters : PhaseParameters) (grade : ℕ) (cell : ℤ) :
    axisWeight parameters grade cell ≤ axisWeight parameters (grade + 1) cell := by
  unfold axisWeight
  have frequencyOne := cellFrequency_one_le cell
  have expPos := (Real.exp_pos (parameters.sigma0 * cellFrequency cell)).le
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ frequencyOne (Nat.le_succ grade)) expPos

theorem axisWeight_even (parameters : PhaseParameters) (grade : ℕ) (cell : ℤ) :
    axisWeight parameters grade (-cell) = axisWeight parameters grade cell := by
  unfold axisWeight
  rw [cellFrequency_neg]

theorem axisWeight_sq (parameters : PhaseParameters) (grade : ℕ) (cell : ℤ) :
    axisWeight parameters grade cell ^ 2 =
      Real.exp (2 * parameters.sigma0 * cellFrequency cell) *
        cellFrequency cell ^ (2 * grade) := by
  unfold axisWeight
  have expSq : Real.exp (parameters.sigma0 * cellFrequency cell) ^ 2 =
      Real.exp (2 * parameters.sigma0 * cellFrequency cell) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have powSq : (cellFrequency cell ^ grade) ^ 2 = cellFrequency cell ^ (2 * grade) := by
    rw [← pow_mul, Nat.mul_comm]
  rw [mul_pow, expSq, powSq]

/-- The literal M16 axis-grade carrier: the weighted exponent-two sequence
Hilbert space, realized as the actual weighted `l2` coefficient space. -/
abbrev AxisGrade (_parameters : PhaseParameters) (valueDimension : ℕ) (_grade : ℕ) :=
  lp (fun _ : ℤ => ComplexEuclidean valueDimension) 2

/-- The literal axis coefficient of a carrier element. -/
def axisCoefficient {valueDimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (field : AxisGrade parameters valueDimension grade) (cell : ℤ) :
    ComplexEuclidean valueDimension :=
  ((axisWeight parameters grade cell : ℂ))⁻¹ • field cell

theorem axis_weighted_coefficient {valueDimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (field : AxisGrade parameters valueDimension grade) (cell : ℤ) :
    (axisWeight parameters grade cell : ℂ) •
      axisCoefficient parameters grade field cell = field cell :=
  smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (axisWeight_pos parameters grade cell).ne') _

/-- The exact M16 norm identity: the carrier norm is literally the
`sum_n exp(2 sigma0 lambda_n) lambda_n^(2q) ||a_n||^2` axis norm of its
coefficients. -/
theorem axis_norm_sq {valueDimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (field : AxisGrade parameters valueDimension grade) :
    ‖field‖ ^ 2 = ∑' cell : ℤ,
      Real.exp (2 * parameters.sigma0 * cellFrequency cell) *
        cellFrequency cell ^ (2 * grade) *
          ‖axisCoefficient parameters grade field cell‖ ^ 2 := by
  have normFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at normFormula
  rw [normFormula]
  congr 1
  funext cell
  rw [← axis_weighted_coefficient parameters grade field cell, norm_smul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (axisWeight_pos parameters grade cell), mul_pow, axisWeight_sq]

/-- The literal isometric identification with plain `l2`: the coefficient of
the weighted carrier element recovers the plain sequence, and the weighted
reconstruction recovers the carrier element, normwise exactly. -/
theorem axis_l2_identification {valueDimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (field : AxisGrade parameters valueDimension grade) :
    (∀ cell, (axisWeight parameters grade cell : ℂ) •
        axisCoefficient parameters grade field cell = field cell) ∧
      ‖field‖ ^ 2 = ∑' cell : ℤ, ‖(axisWeight parameters grade cell : ℂ) •
        axisCoefficient parameters grade field cell‖ ^ 2 := by
  refine ⟨axis_weighted_coefficient parameters grade field, ?_⟩
  have normFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at normFormula
  rw [normFormula]
  congr 1
  funext cell
  rw [axis_weighted_coefficient parameters grade field cell]

end Grad.AxisCore
