import TameCoefficientBounds

noncomputable section

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! The scalar analytic square-root series of Q7–Q8 in the coefficient
algebra: the literal recursion `c₀ = 1`, `c_{p+1} = ((p - 1/2)/(p+1)) c_p`,
its derivative-shifted coefficient families, and the general
series-in-the-core construction with graded envelope majorants. -/

variable {parameters : PhaseParameters}

/-- The literal Q7 recursion. -/
noncomputable def rootCoefficient : ℕ → ℝ
  | 0 => 1
  | p + 1 => ((p : ℝ) - 1 / 2) / ((p : ℝ) + 1) * rootCoefficient p

theorem abs_rootCoefficient_le_one : ∀ p, |rootCoefficient p| ≤ 1 := by
  intro p
  induction p with
  | zero =>
    rw [rootCoefficient]
    norm_num
  | succ smaller inductive_step =>
    rw [rootCoefficient, abs_mul, abs_div]
    have denominator_pos : (0 : ℝ) < (smaller : ℝ) + 1 := by positivity
    have numerator_le : |(smaller : ℝ) - 1 / 2| ≤ (smaller : ℝ) + 1 := by
      rw [abs_le]
      constructor
      · have : (0 : ℝ) ≤ (smaller : ℝ) := Nat.cast_nonneg smaller
        linarith
      · linarith
    have ratio_le_one : |(smaller : ℝ) - 1 / 2| / |(smaller : ℝ) + 1| ≤ 1 := by
      rw [abs_of_pos denominator_pos]
      exact div_le_one_of_le₀ numerator_le denominator_pos.le
    calc |(smaller : ℝ) - 1 / 2| / |(smaller : ℝ) + 1| * |rootCoefficient smaller|
        ≤ 1 * 1 := mul_le_mul ratio_le_one inductive_step (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- The `k`-fold derivative-shifted series coefficient
`c_{p+k} (p+k)(p+k-1) ⋯ (p+1)`. -/
def rootDerivativeCoefficient (order p : ℕ) : ℝ :=
  rootCoefficient (p + order) * ((p + order).descFactorial order : ℝ)

theorem descFactorial_le_pow (n : ℕ) : ∀ k, n.descFactorial k ≤ n ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ smaller inductive_step =>
    rw [Nat.descFactorial_succ, pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul inductive_step (Nat.sub_le n smaller)

theorem abs_rootDerivativeCoefficient_le (order p : ℕ) :
    |rootDerivativeCoefficient order p| ≤ ((p + order : ℕ) : ℝ) ^ order := by
  rw [rootDerivativeCoefficient, abs_mul]
  have factorial_abs : |(((p + order).descFactorial order : ℕ) : ℝ)| =
      (((p + order).descFactorial order : ℕ) : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
  rw [factorial_abs]
  calc |rootCoefficient (p + order)| * (((p + order).descFactorial order : ℕ) : ℝ)
      ≤ 1 * (((p + order : ℕ) : ℝ) ^ order) := by
        apply mul_le_mul (abs_rootCoefficient_le_one _) _ (Nat.cast_nonneg _) zero_le_one
        calc (((p + order).descFactorial order : ℕ) : ℝ)
            ≤ (((p + order) ^ order : ℕ) : ℝ) :=
              Nat.cast_le.mpr (descFactorial_le_pow (p + order) order)
          _ = ((p + order : ℕ) : ℝ) ^ order := by rw [Nat.cast_pow]
    _ = _ := one_mul _

/-- The exact derivative shift: `(p+1) c^{(k)}_{p+1} = c^{(k+1)}_p`. -/
theorem rootDerivativeCoefficient_shift (order p : ℕ) :
    ((p : ℝ) + 1) * rootDerivativeCoefficient order (p + 1) =
      rootDerivativeCoefficient (order + 1) p := by
  rw [rootDerivativeCoefficient, rootDerivativeCoefficient]
  have argument : p + 1 + order = p + (order + 1) := by omega
  have descStep : (p + (order + 1)).descFactorial (order + 1) =
      (p + 1) * (p + (order + 1)).descFactorial order := by
    rw [Nat.descFactorial_succ]
    congr 1
    omega
  rw [argument, descStep]
  push_cast
  ring

/-! ### Series in the coefficient core with graded majorants -/

/-- A graded envelope majorant for a family of coefficient-core terms. -/
def SeriesMajorant {Index : Type} (terms : Index → TameCoefficient parameters)
    (majorant : ℕ → Index → ℝ) : Prop :=
  ∀ grade : ℕ, (∀ index, coefficientEnvelope grade (terms index) ≤ majorant grade index) ∧
    Summable (majorant grade)

theorem SeriesMajorant.nonneg {Index : Type} {terms : Index → TameCoefficient parameters}
    {majorant : ℕ → Index → ℝ} (major : SeriesMajorant terms majorant)
    (grade : ℕ) (index : Index) : 0 ≤ majorant grade index :=
  (coefficientEnvelope_nonneg grade (terms index)).trans ((major grade).1 index)

theorem SeriesMajorant.value_norm_summable {Index : Type}
    {terms : Index → TameCoefficient parameters} {majorant : ℕ → Index → ℝ}
    (major : SeriesMajorant terms majorant) (cell : ℤ) :
    Summable (fun index => ‖(terms index).val cell‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun index => ?_) ((major 0).2)
  exact (norm_le_tameEnvelope (terms index).property 0 cell).trans ((major 0).1 index)

theorem SeriesMajorant.value_summable {Index : Type}
    {terms : Index → TameCoefficient parameters} {majorant : ℕ → Index → ℝ}
    (major : SeriesMajorant terms majorant) (cell : ℤ) :
    Summable (fun index => (terms index).val cell) :=
  Summable.of_norm (major.value_norm_summable cell)

theorem SeriesMajorant.sum_summable_family {Index : Type}
    {terms : Index → TameCoefficient parameters} {majorant : ℕ → Index → ℝ}
    (major : SeriesMajorant terms majorant) :
    TameSummableFamily parameters (fun cell => ∑' index, (terms index).val cell) := by
  intro grade
  apply summable_of_ofReal_tsum_ne_top (tameEnvelopeTerm_nonneg parameters grade _)
  have pointwise (cell : ℤ) : ENNReal.ofReal (tameEnvelopeTerm parameters grade
      (fun cell => ∑' index, (terms index).val cell) cell) ≤
      ∑' index, ENNReal.ofReal (tameEnvelopeTerm parameters grade (terms index).val cell) := by
    calc ENNReal.ofReal (tameEnvelopeTerm parameters grade
          (fun cell => ∑' index, (terms index).val cell) cell)
        ≤ ENNReal.ofReal (tameWeight parameters grade cell *
            ∑' index, ‖(terms index).val cell‖) := by
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_mul_of_nonneg_left
            (norm_tsum_le_tsum_norm (major.value_norm_summable cell))
            (tameWeight_pos parameters grade cell).le
      _ = ∑' index, ENNReal.ofReal (tameWeight parameters grade cell *
            ‖(terms index).val cell‖) := by
          rw [← tsum_mul_left,
            ofReal_tsum_eq_tsum_ofReal (fun index => mul_nonneg
              (tameWeight_pos parameters grade cell).le (norm_nonneg _))
              ((major.value_norm_summable cell).mul_left _)]
      _ = _ := rfl
  apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum pointwise)
  rw [ENNReal.tsum_comm]
  have inner_le (index : Index) : (∑' cell, ENNReal.ofReal
      (tameEnvelopeTerm parameters grade (terms index).val cell)) ≤
      ENNReal.ofReal (majorant grade index) := by
    rw [← ofReal_tsum_eq_tsum_ofReal (tameEnvelopeTerm_nonneg parameters grade _)
      ((terms index).property grade)]
    exact ENNReal.ofReal_le_ofReal ((major grade).1 index)
  apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum inner_le)
  exact ofReal_tsum_ne_top_of_summable (major.nonneg grade) ((major grade).2)

/-- The sum of a majorized series of coefficient-core terms. -/
def tameSeries {Index : Type} (terms : Index → TameCoefficient parameters)
    {majorant : ℕ → Index → ℝ} (major : SeriesMajorant terms majorant) :
    TameCoefficient parameters :=
  ⟨fun cell => ∑' index, (terms index).val cell, major.sum_summable_family⟩

theorem tameSeries_val {Index : Type} (terms : Index → TameCoefficient parameters)
    {majorant : ℕ → Index → ℝ} (major : SeriesMajorant terms majorant) (cell : ℤ) :
    (tameSeries terms major).val cell = ∑' index, (terms index).val cell := rfl

theorem tameSeries_hasSum {Index : Type} (terms : Index → TameCoefficient parameters)
    {majorant : ℕ → Index → ℝ} (major : SeriesMajorant terms majorant) (cell : ℤ) :
    HasSum (fun index => (terms index).val cell) ((tameSeries terms major).val cell) :=
  (major.value_summable cell).hasSum

theorem tameSeries_envelope_le {Index : Type} (terms : Index → TameCoefficient parameters)
    {majorant : ℕ → Index → ℝ} (major : SeriesMajorant terms majorant) (grade : ℕ) :
    coefficientEnvelope grade (tameSeries terms major) ≤ ∑' index, majorant grade index := by
  have rightNonneg : 0 ≤ ∑' index, majorant grade index :=
    tsum_nonneg (major.nonneg grade)
  rw [← ENNReal.ofReal_le_ofReal_iff rightNonneg, coefficientEnvelope, tameEnvelope,
    ofReal_tsum_eq_tsum_ofReal (tameEnvelopeTerm_nonneg parameters grade _)
      ((tameSeries terms major).property grade),
    ofReal_tsum_eq_tsum_ofReal (major.nonneg grade) ((major grade).2)]
  have pointwise (cell : ℤ) : ENNReal.ofReal (tameEnvelopeTerm parameters grade
      (tameSeries terms major).val cell) ≤
      ∑' index, ENNReal.ofReal (tameEnvelopeTerm parameters grade (terms index).val cell) := by
    calc ENNReal.ofReal (tameEnvelopeTerm parameters grade (tameSeries terms major).val cell)
        ≤ ENNReal.ofReal (tameWeight parameters grade cell *
            ∑' index, ‖(terms index).val cell‖) := by
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_mul_of_nonneg_left
            (norm_tsum_le_tsum_norm (major.value_norm_summable cell))
            (tameWeight_pos parameters grade cell).le
      _ = ∑' index, ENNReal.ofReal (tameWeight parameters grade cell *
            ‖(terms index).val cell‖) := by
          rw [← tsum_mul_left,
            ofReal_tsum_eq_tsum_ofReal (fun index => mul_nonneg
              (tameWeight_pos parameters grade cell).le (norm_nonneg _))
              ((major.value_norm_summable cell).mul_left _)]
      _ = _ := rfl
  calc ∑' cell, ENNReal.ofReal (tameEnvelopeTerm parameters grade
        (tameSeries terms major).val cell)
      ≤ ∑' cell, ∑' index, ENNReal.ofReal
          (tameEnvelopeTerm parameters grade (terms index).val cell) :=
        ENNReal.tsum_le_tsum pointwise
    _ = ∑' index, ∑' cell, ENNReal.ofReal
          (tameEnvelopeTerm parameters grade (terms index).val cell) := ENNReal.tsum_comm
    _ ≤ _ := by
        apply ENNReal.tsum_le_tsum
        intro index
        rw [← ofReal_tsum_eq_tsum_ofReal (tameEnvelopeTerm_nonneg parameters grade _)
          ((terms index).property grade)]
        exact ENNReal.ofReal_le_ofReal ((major grade).1 index)

/-- Two majorized series with the same terms are equal. -/
theorem tameSeries_congr {Index : Type} (terms : Index → TameCoefficient parameters)
    {firstMajorant secondMajorant : ℕ → Index → ℝ}
    (firstMajor : SeriesMajorant terms firstMajorant)
    (secondMajor : SeriesMajorant terms secondMajorant) :
    tameSeries terms firstMajor = tameSeries terms secondMajor := Subtype.ext rfl

/-! ### Polynomial–geometric summability -/

theorem summable_succ_pow_mul_geometric (exponent : ℕ) {ratio : ℝ}
    (ratioPos : 0 < ratio) (ratioLt : ratio < 1) :
    Summable (fun p : ℕ => ((p + 1 : ℕ) : ℝ) ^ exponent * ratio ^ p) := by
  have base : Summable (fun n : ℕ => (n : ℝ) ^ exponent * ratio ^ n) := by
    apply summable_pow_mul_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_pos ratioPos]
    exact ratioLt
  have shifted : Summable (fun p : ℕ => ((p + 1 : ℕ) : ℝ) ^ exponent * ratio ^ (p + 1)) := by
    exact (summable_nat_add_iff 1).mpr base
  apply (shifted.mul_left ratio⁻¹).congr
  intro p
  rw [pow_succ]
  field_simp

/-! ### The shifted root series -/

/-- The radius used by the canonical root-series majorant. -/
def rootSmallRadius (x : TameCoefficient parameters) : ℝ :=
  (1 + coefficientEnvelope 0 x) / 2

theorem rootSmallRadius_pos (x : TameCoefficient parameters) : 0 < rootSmallRadius x := by
  have := coefficientEnvelope_nonneg 0 x
  rw [rootSmallRadius]
  linarith

theorem rootSmallRadius_lt_one {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) : rootSmallRadius x < 1 := by
  rw [rootSmallRadius]
  linarith

theorem envelope_le_rootSmallRadius {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) :
    coefficientEnvelope 0 x ≤ rootSmallRadius x := by
  rw [rootSmallRadius]
  linarith

/-- The canonical graded majorant of the `k`-fold shifted root series. -/
def rootSeriesMajorant (order : ℕ) (x : TameCoefficient parameters) :
    ℕ → ℕ → ℝ := fun grade p =>
  match p with
  | 0 => |rootDerivativeCoefficient order 0| * Real.exp parameters.sigma0
  | p + 1 => |rootDerivativeCoefficient order (p + 1)| *
      (((p + 1 : ℕ) : ℝ) ^ (grade + 1) * rootSmallRadius x ^ p *
        coefficientEnvelope grade x)

theorem rootSeriesMajorant_summable (order : ℕ) {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) (grade : ℕ) :
    Summable (rootSeriesMajorant order x grade) := by
  rw [← summable_nat_add_iff 1]
  have comparison : Summable (fun p : ℕ =>
      (((order + 1 : ℕ) : ℝ)) ^ (order + grade + 2) *
        (((p + 1 : ℕ) : ℝ) ^ (order + grade + 2) * rootSmallRadius x ^ p) *
        coefficientEnvelope grade x) := by
    apply Summable.mul_right
    apply Summable.mul_left
    exact summable_succ_pow_mul_geometric (order + grade + 2)
      (rootSmallRadius_pos x) (rootSmallRadius_lt_one small)
  apply Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) comparison
  · rw [rootSeriesMajorant]
    apply mul_nonneg (abs_nonneg _)
    apply mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (pow_nonneg (rootSmallRadius_pos x).le _)) (coefficientEnvelope_nonneg _ _)
  · rw [rootSeriesMajorant]
    have coefficient_le : |rootDerivativeCoefficient order (p + 1)| ≤
        ((p + 1 + order : ℕ) : ℝ) ^ order := abs_rootDerivativeCoefficient_le order (p + 1)
    have split_le : ((p + 1 + order : ℕ) : ℝ) ^ order ≤
        (((order + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ)) ^ order := by
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) p, Nat.cast_nonneg (α := ℝ) order]
    calc |rootDerivativeCoefficient order (p + 1)| *
          (((p + 1 : ℕ) : ℝ) ^ (grade + 1) * rootSmallRadius x ^ p *
            coefficientEnvelope grade x)
        ≤ ((((order + 1 : ℕ) : ℝ) * ((p + 1 : ℕ) : ℝ)) ^ order) *
          (((p + 1 : ℕ) : ℝ) ^ (grade + 1) * rootSmallRadius x ^ p *
            coefficientEnvelope grade x) := by
          apply mul_le_mul_of_nonneg_right (coefficient_le.trans split_le)
          apply mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
            (pow_nonneg (rootSmallRadius_pos x).le _)) (coefficientEnvelope_nonneg _ _)
      _ ≤ _ := by
          rw [mul_pow]
          have first_le : (((order + 1 : ℕ) : ℝ)) ^ order ≤
              (((order + 1 : ℕ) : ℝ)) ^ (order + grade + 2) := by
            apply pow_le_pow_right₀ _ (by omega)
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero order)
          have second_le : (((p + 1 : ℕ) : ℝ)) ^ order * (((p + 1 : ℕ) : ℝ)) ^ (grade + 1) ≤
              (((p + 1 : ℕ) : ℝ)) ^ (order + grade + 2) := by
            rw [← pow_add]
            apply pow_le_pow_right₀ _ (by omega)
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero p)
          have combined : (((order + 1 : ℕ) : ℝ)) ^ order * (((p + 1 : ℕ) : ℝ)) ^ order *
              (((p + 1 : ℕ) : ℝ)) ^ (grade + 1) ≤
              (((order + 1 : ℕ) : ℝ)) ^ (order + grade + 2) *
                (((p + 1 : ℕ) : ℝ)) ^ (order + grade + 2) := by
            rw [mul_assoc]
            exact mul_le_mul first_le second_le
              (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
                (pow_nonneg (Nat.cast_nonneg _) _))
              (pow_nonneg (Nat.cast_nonneg _) _)
          have tail_nonneg : (0 : ℝ) ≤ rootSmallRadius x ^ p * coefficientEnvelope grade x :=
            mul_nonneg (pow_nonneg (rootSmallRadius_pos x).le p)
              (coefficientEnvelope_nonneg grade x)
          calc (((order + 1 : ℕ) : ℝ)) ^ order * (((p + 1 : ℕ) : ℝ)) ^ order *
                ((((p + 1 : ℕ) : ℝ)) ^ (grade + 1) * rootSmallRadius x ^ p *
                  coefficientEnvelope grade x)
              = ((((order + 1 : ℕ) : ℝ)) ^ order * (((p + 1 : ℕ) : ℝ)) ^ order *
                  (((p + 1 : ℕ) : ℝ)) ^ (grade + 1)) *
                (rootSmallRadius x ^ p * coefficientEnvelope grade x) := by ring
            _ ≤ ((((order + 1 : ℕ) : ℝ)) ^ (order + grade + 2) *
                  (((p + 1 : ℕ) : ℝ)) ^ (order + grade + 2)) *
                (rootSmallRadius x ^ p * coefficientEnvelope grade x) :=
                mul_le_mul_of_nonneg_right combined tail_nonneg
            _ = _ := by ring

theorem rootSeries_term_envelope_le (order : ℕ) {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) (grade p : ℕ) :
    coefficientEnvelope grade (((rootDerivativeCoefficient order p : ℝ) : ℂ) • x ^ p) ≤
      rootSeriesMajorant order x grade p := by
  rw [coefficientEnvelope_smul]
  have coefficient_norm : ‖((rootDerivativeCoefficient order p : ℝ) : ℂ)‖ =
      |rootDerivativeCoefficient order p| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [coefficient_norm]
  match p with
  | 0 =>
    rw [rootSeriesMajorant, pow_zero, coefficientEnvelope_one]
  | p + 1 =>
    rw [rootSeriesMajorant]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc coefficientEnvelope grade (x ^ (p + 1))
        ≤ ((p + 1 : ℕ) : ℝ) ^ (grade + 1) *
            coefficientEnvelope 0 x ^ p * coefficientEnvelope grade x :=
          tamePow_envelope_le grade p x
      _ ≤ _ := by
          rw [mul_assoc, mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) _)
          apply mul_le_mul_of_nonneg_right _ (coefficientEnvelope_nonneg _ _)
          exact pow_le_pow_left₀ (coefficientEnvelope_nonneg _ _)
            (envelope_le_rootSmallRadius small) p

/-- The root-series majorant certificate. -/
theorem rootSeriesMajorant_is_majorant (order : ℕ) {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) :
    SeriesMajorant (fun p => ((rootDerivativeCoefficient order p : ℝ) : ℂ) • x ^ p)
      (rootSeriesMajorant order x) := by
  intro grade
  exact ⟨fun p => rootSeries_term_envelope_le order small grade p,
    rootSeriesMajorant_summable order small grade⟩

/-- The `k`-fold shifted root series `G_k(x) = Σ_p c^{(k)}_p x^p` on the
fixed grade-zero ball. -/
def rootShiftedSeries (order : ℕ) (x : TameCoefficient parameters)
    (small : coefficientEnvelope 0 x < 1) : TameCoefficient parameters :=
  tameSeries (fun p => ((rootDerivativeCoefficient order p : ℝ) : ℂ) • x ^ p)
    (rootSeriesMajorant_is_majorant order small)

theorem rootShiftedSeries_hasSum (order : ℕ) (x : TameCoefficient parameters)
    (small : coefficientEnvelope 0 x < 1) (cell : ℤ) :
    HasSum (fun p => (((rootDerivativeCoefficient order p : ℝ) : ℂ) • x ^ p).val cell)
      ((rootShiftedSeries order x small).val cell) :=
  tameSeries_hasSum _ _ cell

theorem rootShiftedSeries_envelope_le (order : ℕ) (x : TameCoefficient parameters)
    (small : coefficientEnvelope 0 x < 1) (grade : ℕ) :
    coefficientEnvelope grade (rootShiftedSeries order x small) ≤
      ∑' p, rootSeriesMajorant order x grade p :=
  tameSeries_envelope_le _ _ grade

/-- The square root series itself: `F = G₀`. -/
def rootSeries (x : TameCoefficient parameters)
    (small : coefficientEnvelope 0 x < 1) : TameCoefficient parameters :=
  rootShiftedSeries 0 x small

end Grad.NonlinearQuotientBounds
