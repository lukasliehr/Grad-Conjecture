import MajorantInterface

/-!
# NG_F06: the Q8 placement estimate for the derivative terms

The accepted Q6 one-high estimates (`tamePow_envelope_le`,
`tamePow_envelope_zero_le`, `tameProd_envelope_le`, `tameProd_envelope_zero_le`,
`tameMul_envelope_le`) bound the grade-`s` envelope of
`x^{p-j} · h_1 ⋯ h_j` on the ball `|x|_0 ≤ θ'`, `|x|_s ≤ R` by
`2^s e^{2σ₀} [ (p-j+1)^{s+1} (R+1) θ'^{p-j-1} + (j+1)^{s+1} θ'^{p-j} ] ∏_i |h_i|_s`:
the high slot on `x` costs `θ'^{p-j-1}`, the high slot on a direction costs
`θ'^{p-j}`. Multiplied by `|c_p| p^{\underline j}` this is the majorant
`rootOperatorMajorant`.
-/

noncomputable section

open scoped BigOperators

namespace Grad.CoefficientMajorants

open Grad.NonlinearQuotientBounds Grad.CartesianState

variable {parameters : PhaseParameters}

theorem one_le_exp_sigma0 (parameters : PhaseParameters) : 1 ≤ Real.exp parameters.sigma0 :=
  Real.one_le_exp parameters.sigma0_pos.le

/-- High-grade envelope of a power on the ball: `e^{σ₀} (n+1)^{s+1} (R+1) θ'^{n-1}`. -/
theorem envelope_pow_high_le (grade n : ℕ) {theta radius : ℝ} (thetaNonneg : 0 ≤ theta)
    (radiusNonneg : 0 ≤ radius) {x : TameCoefficient parameters}
    (lowBall : coefficientEnvelope 0 x ≤ theta) (highBall : coefficientEnvelope grade x ≤ radius) :
    coefficientEnvelope grade (x ^ n) ≤
      Real.exp parameters.sigma0 *
        (((n + 1 : ℕ) : ℝ) ^ (grade + 1) * (radius + 1) * theta ^ (n - 1)) := by
  have expOne := one_le_exp_sigma0 parameters
  cases n with
  | zero =>
    rw [pow_zero, coefficientEnvelope_one]
    simp only [Nat.zero_add, Nat.cast_one, one_pow, one_mul, Nat.zero_sub, pow_zero, mul_one]
    exact le_mul_of_one_le_right (Real.exp_pos _).le (by linarith)
  | succ m =>
    have master := tamePow_envelope_le grade m x
    have lowPow : coefficientEnvelope 0 x ^ m ≤ theta ^ m :=
      pow_le_pow_left₀ (coefficientEnvelope_nonneg 0 x) lowBall m
    have basePow : ((m + 1 : ℕ) : ℝ) ^ (grade + 1) ≤ ((m + 1 + 1 : ℕ) : ℝ) ^ (grade + 1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.le_succ _) _
    have thetaPow : 0 ≤ theta ^ m := pow_nonneg thetaNonneg m
    rw [Nat.add_sub_cancel]
    calc coefficientEnvelope grade (x ^ (m + 1))
        ≤ ((m + 1 : ℕ) : ℝ) ^ (grade + 1) * coefficientEnvelope 0 x ^ m *
            coefficientEnvelope grade x := master
      _ ≤ ((m + 1 + 1 : ℕ) : ℝ) ^ (grade + 1) * theta ^ m * (radius + 1) := by
          apply mul_le_mul _ (by linarith) (coefficientEnvelope_nonneg _ _)
            (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) thetaPow)
          exact mul_le_mul basePow lowPow (pow_nonneg (coefficientEnvelope_nonneg _ _) _)
            (pow_nonneg (Nat.cast_nonneg _) _)
      _ = 1 * (((m + 1 + 1 : ℕ) : ℝ) ^ (grade + 1) * (radius + 1) * theta ^ m) := by ring
      _ ≤ Real.exp parameters.sigma0 *
            (((m + 1 + 1 : ℕ) : ℝ) ^ (grade + 1) * (radius + 1) * theta ^ m) := by
          apply mul_le_mul_of_nonneg_right expOne
          apply mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (by linarith)) thetaPow

/-- Low-grade envelope of a power on the ball: `e^{σ₀} θ'^n`. -/
theorem envelope_pow_low_le (n : ℕ) {theta : ℝ} (thetaNonneg : 0 ≤ theta)
    {x : TameCoefficient parameters} (lowBall : coefficientEnvelope 0 x ≤ theta) :
    coefficientEnvelope 0 (x ^ n) ≤ Real.exp parameters.sigma0 * theta ^ n := by
  have expOne := one_le_exp_sigma0 parameters
  cases n with
  | zero =>
    rw [pow_zero, coefficientEnvelope_one, pow_zero, mul_one]
  | succ m =>
    calc coefficientEnvelope 0 (x ^ (m + 1))
        ≤ coefficientEnvelope 0 x ^ (m + 1) := tamePow_envelope_zero_le m x
      _ ≤ theta ^ (m + 1) := pow_le_pow_left₀ (coefficientEnvelope_nonneg 0 x) lowBall _
      _ = 1 * theta ^ (m + 1) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right expOne (pow_nonneg thetaNonneg _)

/-- High-grade envelope of a product of directions:
`e^{σ₀} (j+1)^{s+1} ∏_i |h_i|_s`. -/
theorem envelope_prod_high_le (grade order : ℕ)
    (directions : Fin order → TameCoefficient parameters) :
    coefficientEnvelope grade (∏ index, directions index) ≤
      Real.exp parameters.sigma0 *
        (((order + 1 : ℕ) : ℝ) ^ (grade + 1) *
          ∏ index, coefficientEnvelope grade (directions index)) := by
  have expOne := one_le_exp_sigma0 parameters
  cases order with
  | zero =>
    rw [Fin.prod_univ_zero, Fin.prod_univ_zero, coefficientEnvelope_one]
    simp
  | succ m =>
    have master := tameProd_envelope_le grade (smaller := m) directions
    have productNonneg : 0 ≤ ∏ index, coefficientEnvelope grade (directions index) :=
      Finset.prod_nonneg fun _ _ => coefficientEnvelope_nonneg _ _
    have summand (index : Fin (m + 1)) :
        coefficientEnvelope grade (directions index) *
          ∏ other ∈ Finset.univ.erase index, coefficientEnvelope 0 (directions other) ≤
        ∏ index, coefficientEnvelope grade (directions index) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun index => coefficientEnvelope grade
        (directions index)) (Finset.mem_univ index)]
      apply mul_le_mul_of_nonneg_left _ (coefficientEnvelope_nonneg _ _)
      exact Finset.prod_le_prod (fun _ _ => coefficientEnvelope_nonneg _ _)
        (fun other _ => coefficientEnvelope_mono (Nat.zero_le grade) (directions other))
    have sumBound : (∑ index, coefficientEnvelope grade (directions index) *
        ∏ other ∈ Finset.univ.erase index, coefficientEnvelope 0 (directions other)) ≤
        ((m + 1 : ℕ) : ℝ) * ∏ index, coefficientEnvelope grade (directions index) := by
      calc _ ≤ ∑ _index : Fin (m + 1), ∏ index, coefficientEnvelope grade (directions index) :=
            Finset.sum_le_sum fun index _ => summand index
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have basePow : ((m + 1 : ℕ) : ℝ) ^ (grade + 1) ≤ ((m + 1 + 1 : ℕ) : ℝ) ^ (grade + 1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.le_succ _) _
    calc coefficientEnvelope grade (∏ index, directions index)
        ≤ ((m + 1 : ℕ) : ℝ) ^ grade * ∑ index, coefficientEnvelope grade (directions index) *
            ∏ other ∈ Finset.univ.erase index, coefficientEnvelope 0 (directions other) := master
      _ ≤ ((m + 1 : ℕ) : ℝ) ^ grade *
            (((m + 1 : ℕ) : ℝ) * ∏ index, coefficientEnvelope grade (directions index)) :=
          mul_le_mul_of_nonneg_left sumBound (pow_nonneg (Nat.cast_nonneg _) _)
      _ = ((m + 1 : ℕ) : ℝ) ^ (grade + 1) * ∏ index, coefficientEnvelope grade (directions index) := by
          rw [pow_succ]
          ring
      _ ≤ 1 * (((m + 1 + 1 : ℕ) : ℝ) ^ (grade + 1) *
            ∏ index, coefficientEnvelope grade (directions index)) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_right basePow productNonneg
      _ ≤ _ := mul_le_mul_of_nonneg_right expOne
          (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) productNonneg)

/-- Low-grade envelope of a product of directions: `e^{σ₀} ∏_i |h_i|_s`. -/
theorem envelope_prod_low_le (grade order : ℕ)
    (directions : Fin order → TameCoefficient parameters) :
    coefficientEnvelope 0 (∏ index, directions index) ≤
      Real.exp parameters.sigma0 * ∏ index, coefficientEnvelope grade (directions index) := by
  have expOne := one_le_exp_sigma0 parameters
  cases order with
  | zero =>
    rw [Fin.prod_univ_zero, Fin.prod_univ_zero, coefficientEnvelope_one, mul_one]
  | succ m =>
    have productNonneg : 0 ≤ ∏ index, coefficientEnvelope grade (directions index) :=
      Finset.prod_nonneg fun _ _ => coefficientEnvelope_nonneg _ _
    calc coefficientEnvelope 0 (∏ index, directions index)
        ≤ ∏ index, coefficientEnvelope 0 (directions index) :=
          tameProd_envelope_zero_le (smaller := m) directions
      _ ≤ ∏ index, coefficientEnvelope grade (directions index) :=
          Finset.prod_le_prod (fun _ _ => coefficientEnvelope_nonneg _ _)
            (fun index _ => coefficientEnvelope_mono (Nat.zero_le grade) (directions index))
      _ = 1 * ∏ index, coefficientEnvelope grade (directions index) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right expOne productNonneg

/-- The Q8 placement estimate: the grade-`s` envelope of the derivative term is
dominated by the explicit majorant times `∏_i |h_i|_s`, uniformly on the ball. -/
theorem rootDerivativeTerm_envelope_le (grade order p : ℕ) {theta radius : ℝ}
    (thetaNonneg : 0 ≤ theta) (radiusNonneg : 0 ≤ radius) {x : TameCoefficient parameters}
    (lowBall : coefficientEnvelope 0 x ≤ theta) (highBall : coefficientEnvelope grade x ≤ radius)
    (directions : Fin order → TameCoefficient parameters) :
    coefficientEnvelope grade (rootDerivativeTerm order p x directions) ≤
      rootOperatorMajorant parameters grade order theta radius p *
        ∏ index, coefficientEnvelope grade (directions index) := by
  unfold rootDerivativeTerm rootOperatorMajorant
  rw [coefficientEnvelope_smul, Complex.norm_real, Real.norm_eq_abs, abs_mul, Nat.abs_cast]
  set n := p - order with n_def
  set product := ∏ index, coefficientEnvelope grade (directions index) with product_def
  have productNonneg : 0 ≤ product :=
    Finset.prod_nonneg fun _ _ => coefficientEnvelope_nonneg _ _
  have expNonneg : 0 ≤ Real.exp parameters.sigma0 := (Real.exp_pos _).le
  have first := envelope_pow_high_le grade n thetaNonneg radiusNonneg lowBall highBall
  have second := envelope_prod_low_le grade order directions
  have third := envelope_pow_low_le n thetaNonneg lowBall
  have fourth := envelope_prod_high_le grade order directions
  rw [← product_def] at second fourth
  have binary := tameMul_envelope_le grade (x ^ n) (∏ index, directions index)
  have firstNonneg : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ (grade + 1) * (radius + 1) * theta ^ (n - 1) :=
    mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (by linarith))
      (pow_nonneg thetaNonneg _)
  have thirdNonneg : 0 ≤ theta ^ n := pow_nonneg thetaNonneg n
  have fourthNonneg : 0 ≤ ((order + 1 : ℕ) : ℝ) ^ (grade + 1) * product :=
    mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) productNonneg
  have combined : coefficientEnvelope grade (x ^ n * ∏ index, directions index) ≤
      (2 : ℝ) ^ grade * Real.exp parameters.sigma0 ^ 2 *
        (((n + 1 : ℕ) : ℝ) ^ (grade + 1) * (radius + 1) * theta ^ (n - 1) +
          ((order + 1 : ℕ) : ℝ) ^ (grade + 1) * theta ^ n) * product := by
    calc coefficientEnvelope grade (x ^ n * ∏ index, directions index)
        ≤ (2 : ℝ) ^ grade *
            (coefficientEnvelope grade (x ^ n) * coefficientEnvelope 0 (∏ index, directions index) +
              coefficientEnvelope 0 (x ^ n) * coefficientEnvelope grade (∏ index, directions index)) :=
          binary
      _ ≤ (2 : ℝ) ^ grade *
            ((Real.exp parameters.sigma0 *
                (((n + 1 : ℕ) : ℝ) ^ (grade + 1) * (radius + 1) * theta ^ (n - 1))) *
                (Real.exp parameters.sigma0 * product) +
              (Real.exp parameters.sigma0 * theta ^ n) *
                (Real.exp parameters.sigma0 * (((order + 1 : ℕ) : ℝ) ^ (grade + 1) * product))) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
          apply add_le_add
          · exact mul_le_mul first second (coefficientEnvelope_nonneg _ _)
              (mul_nonneg expNonneg firstNonneg)
          · exact mul_le_mul third fourth (coefficientEnvelope_nonneg _ _)
              (mul_nonneg expNonneg thirdNonneg)
      _ = _ := by ring
  calc |rootCoefficient p| * (p.descFactorial order : ℝ) *
        coefficientEnvelope grade (x ^ n * ∏ index, directions index)
      ≤ |rootCoefficient p| * (p.descFactorial order : ℝ) *
        ((2 : ℝ) ^ grade * Real.exp parameters.sigma0 ^ 2 *
          (((n + 1 : ℕ) : ℝ) ^ (grade + 1) * (radius + 1) * theta ^ (n - 1) +
            ((order + 1 : ℕ) : ℝ) ^ (grade + 1) * theta ^ n) * product) :=
        mul_le_mul_of_nonneg_left combined (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    _ = _ := by ring

end Grad.CoefficientMajorants
