import FC2Phase

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.PhaseAlgebra

open Grad.CartesianState

/-- The literal K1 width `omega(r) = sigma0 - gamma r`. -/
def phaseWidth (parameters : PhaseParameters) (radius : ℝ) : ℝ :=
  parameters.sigma0 - parameters.gamma * radius

theorem phaseWidth_nonneg (parameters : PhaseParameters) (radius : ℝ)
    (_lower : 0 ≤ radius) (upper : radius ≤ 1) : 0 ≤ phaseWidth parameters radius := by
  unfold phaseWidth
  have gammaSigma := parameters_gamma_lt_sigma0 parameters
  have gammaNonneg := parameters_gamma_nonnegative parameters
  nlinarith [mul_nonneg gammaNonneg (sub_nonneg.mpr upper)]

theorem phaseWidth_le_sigma0 (parameters : PhaseParameters) (radius : ℝ)
    (lower : 0 ≤ radius) : phaseWidth parameters radius ≤ parameters.sigma0 := by
  unfold phaseWidth
  have := mul_nonneg (parameters_gamma_nonnegative parameters) lower
  linarith

/-- The manuscript phase at fixed radius: `Phi_r(n)`. -/
def radialPhase (parameters : PhaseParameters) (radius : ℝ) (cell : ℤ) : ℝ :=
  parameters.sigma0 * cellFrequency cell -
    parameters.gamma * (Real.sqrt (1 + cellFrequency cell ^ 2 * radius ^ 2) - 1)

/-- The radial phase is the accepted Cartesian phase at any point of that
norm. -/
theorem radialPhase_eq_cartesianPhase (parameters : PhaseParameters) (radius : ℝ)
    (cell : ℤ) (point : Grad.ClosedJets.SpatialPlane) (radiusNorm : ‖point‖ = radius) :
    cartesianPhase parameters cell point = radialPhase parameters radius cell := by
  rw [cartesianPhase_formula, radiusNorm]
  rfl

theorem radialPhase_neg (parameters : PhaseParameters) (radius : ℝ) (cell : ℤ) :
    radialPhase parameters radius (-cell) = radialPhase parameters radius cell := by
  unfold radialPhase
  rw [cellFrequency_neg]

/-- The concave gap `h(t) = 1 + t - sqrt (1 + t^2)`. -/
def concaveGap (t : ℝ) : ℝ := 1 + t - Real.sqrt (1 + t ^ 2)

theorem sqrt_one_add_sq_le (t : ℝ) (nonneg : 0 ≤ t) :
    Real.sqrt (1 + t ^ 2) ≤ 1 + t := by
  have compare : Real.sqrt (1 + t ^ 2) ≤ Real.sqrt ((1 + t) ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  rwa [Real.sqrt_sq (by linarith)] at compare

theorem le_sqrt_one_add_sq (t : ℝ) (nonneg : 0 ≤ t) : t ≤ Real.sqrt (1 + t ^ 2) := by
  have compare : Real.sqrt (t ^ 2) ≤ Real.sqrt (1 + t ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  rwa [Real.sqrt_sq nonneg] at compare

theorem one_le_sqrt_one_add_sq (t : ℝ) : 1 ≤ Real.sqrt (1 + t ^ 2) := by
  have compare : Real.sqrt 1 ≤ Real.sqrt (1 + t ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])
  rwa [Real.sqrt_one] at compare

theorem concaveGap_nonneg (t : ℝ) (nonneg : 0 ≤ t) : 0 ≤ concaveGap t := by
  unfold concaveGap
  have := sqrt_one_add_sq_le t nonneg
  linarith

theorem concaveGap_le_one (t : ℝ) (nonneg : 0 ≤ t) : concaveGap t ≤ 1 := by
  unfold concaveGap
  have := le_sqrt_one_add_sq t nonneg
  linarith

/-- The exact decomposition `Phi_r(n) = omega(r) lambda_n + gamma h(r lambda_n)`. -/
theorem radialPhase_decompose (parameters : PhaseParameters) (radius : ℝ) (cell : ℤ) :
    radialPhase parameters radius cell =
      phaseWidth parameters radius * cellFrequency cell +
        parameters.gamma * concaveGap (radius * cellFrequency cell) := by
  unfold radialPhase phaseWidth concaveGap
  have square : (radius * cellFrequency cell) ^ 2 =
      cellFrequency cell ^ 2 * radius ^ 2 := by ring
  rw [square]
  ring

/-- K1: the frequency is at most the polynomial weight. -/
theorem cellFrequency_le_polynomial (cell : ℤ) :
    cellFrequency cell ≤ cellPolynomialWeight cell := by
  rw [cellFrequency_formula, cellPolynomialWeight_formula]
  have bound := sqrt_one_add_sq_le |(cell : ℝ)| (abs_nonneg _)
  rwa [sq_abs] at bound

/-- K1: the polynomial weight is at most `sqrt 2` times the frequency. -/
theorem polynomial_le_sqrt_two_mul (cell : ℤ) :
    cellPolynomialWeight cell ≤ Real.sqrt 2 * cellFrequency cell := by
  rw [cellFrequency_formula, cellPolynomialWeight_formula]
  have product : Real.sqrt 2 * Real.sqrt (1 + (cell : ℝ) ^ 2) =
      Real.sqrt (2 * (1 + (cell : ℝ) ^ 2)) :=
    (Real.sqrt_mul (by norm_num) _).symm
  rw [product]
  have compare : Real.sqrt ((1 + |(cell : ℝ)|) ^ 2) ≤
      Real.sqrt (2 * (1 + (cell : ℝ) ^ 2)) := by
    apply Real.sqrt_le_sqrt
    nlinarith [sq_abs (cell : ℝ), sq_nonneg (|(cell : ℝ)| - 1), abs_nonneg (cell : ℝ)]
  rwa [Real.sqrt_sq (by positivity)] at compare

/-- The equivalent analytic weight `w_r(n) = exp (omega(r) |n|)`. -/
def phaseWeight (parameters : PhaseParameters) (radius : ℝ) (cell : ℤ) : ℝ :=
  Real.exp (phaseWidth parameters radius * |(cell : ℝ)|)

theorem phaseWeight_pos (parameters : PhaseParameters) (radius : ℝ) (cell : ℤ) :
    0 < phaseWeight parameters radius cell := Real.exp_pos _

theorem phaseWeight_zero (parameters : PhaseParameters) (radius : ℝ) :
    phaseWeight parameters radius 0 = 1 := by
  unfold phaseWeight
  norm_num

theorem phaseWeight_neg (parameters : PhaseParameters) (radius : ℝ) (cell : ℤ) :
    phaseWeight parameters radius (-cell) = phaseWeight parameters radius cell := by
  unfold phaseWeight
  rw [Int.cast_neg, abs_neg]

/-- K1: unit weight at zero and submultiplicativity of the weight. -/
theorem phaseWeight_submultiplicative (parameters : PhaseParameters) (radius : ℝ)
    (lower : 0 ≤ radius) (upper : radius ≤ 1) (n m : ℤ) :
    phaseWeight parameters radius (n + m) ≤
      phaseWeight parameters radius n * phaseWeight parameters radius m := by
  unfold phaseWeight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have widthNonneg := phaseWidth_nonneg parameters radius lower upper
  have triangle : |((n + m : ℤ) : ℝ)| ≤ |(n : ℝ)| + |(m : ℝ)| := by
    push_cast
    exact abs_add_le _ _
  calc phaseWidth parameters radius * |((n + m : ℤ) : ℝ)|
      ≤ phaseWidth parameters radius * (|(n : ℝ)| + |(m : ℝ)|) :=
        mul_le_mul_of_nonneg_left triangle widthNonneg
    _ = phaseWidth parameters radius * |(n : ℝ)| +
          phaseWidth parameters radius * |(m : ℝ)| := by ring

theorem abs_le_cellFrequency (cell : ℤ) : |(cell : ℝ)| ≤ cellFrequency cell := by
  have bound := le_sqrt_one_add_sq |(cell : ℝ)| (abs_nonneg _)
  rwa [sq_abs, ← cellFrequency_formula] at bound

theorem cellFrequency_le_abs_add_one (cell : ℤ) :
    cellFrequency cell ≤ |(cell : ℝ)| + 1 := by
  have bound := sqrt_one_add_sq_le |(cell : ℝ)| (abs_nonneg _)
  rw [sq_abs, ← cellFrequency_formula] at bound
  linarith

/-- K1 lower comparison: `w_r(n) <= exp (Phi_r(n))`. -/
theorem phaseWeight_le_exp_radialPhase (parameters : PhaseParameters) (radius : ℝ)
    (lower : 0 ≤ radius) (upper : radius ≤ 1) (cell : ℤ) :
    phaseWeight parameters radius cell ≤
      Real.exp (radialPhase parameters radius cell) := by
  apply Real.exp_le_exp.mpr
  rw [radialPhase_decompose]
  have widthNonneg := phaseWidth_nonneg parameters radius lower upper
  have widthTerm : phaseWidth parameters radius * |(cell : ℝ)| ≤
      phaseWidth parameters radius * cellFrequency cell :=
    mul_le_mul_of_nonneg_left (abs_le_cellFrequency cell) widthNonneg
  have gapTerm : 0 ≤ parameters.gamma * concaveGap (radius * cellFrequency cell) :=
    mul_nonneg (parameters_gamma_nonnegative parameters)
      (concaveGap_nonneg _ (mul_nonneg lower (cellFrequency_pos cell).le))
  linarith

/-- K1 upper comparison: `exp (Phi_r(n)) <= exp (sigma0 + gamma) w_r(n)`. -/
theorem exp_radialPhase_le (parameters : PhaseParameters) (radius : ℝ)
    (lower : 0 ≤ radius) (upper : radius ≤ 1) (cell : ℤ) :
    Real.exp (radialPhase parameters radius cell) ≤
      Real.exp (parameters.sigma0 + parameters.gamma) *
        phaseWeight parameters radius cell := by
  unfold phaseWeight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [radialPhase_decompose]
  have widthNonneg := phaseWidth_nonneg parameters radius lower upper
  have widthLe := phaseWidth_le_sigma0 parameters radius lower
  have widthTerm : phaseWidth parameters radius * cellFrequency cell ≤
      phaseWidth parameters radius * (|(cell : ℝ)| + 1) :=
    mul_le_mul_of_nonneg_left (cellFrequency_le_abs_add_one cell) widthNonneg
  have expand : phaseWidth parameters radius * (|(cell : ℝ)| + 1) =
      phaseWidth parameters radius * |(cell : ℝ)| + phaseWidth parameters radius := by
    ring
  have gapTerm : parameters.gamma * concaveGap (radius * cellFrequency cell) ≤
      parameters.gamma :=
    calc parameters.gamma * concaveGap (radius * cellFrequency cell)
        ≤ parameters.gamma * 1 :=
          mul_le_mul_of_nonneg_left
            (concaveGap_le_one _ (mul_nonneg lower (cellFrequency_pos cell).le))
            (parameters_gamma_nonnegative parameters)
      _ = parameters.gamma := mul_one _
  linarith

end Grad.PhaseAlgebra
