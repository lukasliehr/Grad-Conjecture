import QuotientConstantFields
import ProductFiniteTensorSum
import AW1Submultiplicative

noncomputable section

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! The scalar cell-coefficient algebra of the Q5 norms: weighted `ℓ¹`
families over the cells, their convolution products of every arity, and the
exact Q6 one-high estimates with polynomial-in-arity constants.  The weight is
the literal envelope weight `e^{σ₀ λ_n} μ_n^s` of the accepted N2/N6–N9
multiplier calculus, so every bound feeds the accepted `smoothMultiplier`
without translation. -/

/-- The literal envelope weight `e^{σ₀ λ_cell} μ_cell ^ grade`. -/
def tameWeight (parameters : PhaseParameters) (grade : ℕ) (cell : ℤ) : ℝ :=
  Real.exp (parameters.sigma0 * cellFrequency cell) * cellPolynomialWeight cell ^ grade

theorem cellPolynomialWeight_one_le (cell : ℤ) : 1 ≤ cellPolynomialWeight cell := by
  unfold cellPolynomialWeight
  have := abs_nonneg ((cell : ℝ))
  linarith

theorem cellPolynomialWeight_pos (cell : ℤ) : 0 < cellPolynomialWeight cell :=
  lt_of_lt_of_le zero_lt_one (cellPolynomialWeight_one_le cell)

theorem tameWeight_pos (parameters : PhaseParameters) (grade : ℕ) (cell : ℤ) :
    0 < tameWeight parameters grade cell :=
  mul_pos (Real.exp_pos _) (pow_pos (cellPolynomialWeight_pos cell) grade)

theorem tameWeight_one_le (parameters : PhaseParameters) (grade : ℕ) (cell : ℤ) :
    1 ≤ tameWeight parameters grade cell := by
  have exponent_nonneg : 0 ≤ parameters.sigma0 * cellFrequency cell :=
    mul_nonneg parameters.sigma0_pos.le (Grad.CellWeights.cellWeight_pos cell).le
  have exp_one_le : 1 ≤ Real.exp (parameters.sigma0 * cellFrequency cell) :=
    Real.one_le_exp exponent_nonneg
  have power_one_le : 1 ≤ cellPolynomialWeight cell ^ grade :=
    one_le_pow₀ (cellPolynomialWeight_one_le cell)
  calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
  _ ≤ _ := mul_le_mul exp_one_le power_one_le zero_le_one (Real.exp_pos _).le

theorem tameWeight_mono (parameters : PhaseParameters) {lower upper : ℕ}
    (gradeLe : lower ≤ upper) (cell : ℤ) :
    tameWeight parameters lower cell ≤ tameWeight parameters upper cell :=
  mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (cellPolynomialWeight_one_le cell) gradeLe) (Real.exp_pos _).le

theorem cellFrequency_add_le (first second : ℤ) :
    cellFrequency (first + second) ≤ cellFrequency first + cellFrequency second :=
  Grad.AnalyticWeights.cellWeight_add_le first second

/-- Grade-zero submultiplicativity of the weight along cell addition. -/
theorem tameWeight_zero_add_le (parameters : PhaseParameters) (first second : ℤ) :
    tameWeight parameters 0 (first + second) ≤
      tameWeight parameters 0 first * tameWeight parameters 0 second := by
  unfold tameWeight
  simp only [pow_zero, mul_one]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (cellFrequency_add_le first second) parameters.sigma0_pos.le

theorem cellPolynomialWeight_add_le (first second : ℤ) :
    cellPolynomialWeight (first + second) ≤
      cellPolynomialWeight first + cellPolynomialWeight second := by
  unfold cellPolynomialWeight
  have triangle : |((first + second : ℤ) : ℝ)| ≤ |(first : ℝ)| + |(second : ℝ)| := by
    push_cast
    exact abs_add_le _ _
  linarith

theorem cellFrequency_tuple_le (smaller : ℕ) (cells : Fin (smaller + 1) → ℤ) :
    cellFrequency (∑ index, cells index) ≤ ∑ index, cellFrequency (cells index) := by
  induction smaller with
  | zero =>
    simp
  | succ inner inductive_step =>
    have tail_le : cellFrequency (∑ index : Fin (inner + 1), cells index.succ) ≤
        ∑ index : Fin (inner + 1), cellFrequency (cells index.succ) :=
      inductive_step (fun index => cells index.succ)
    calc cellFrequency (∑ index, cells index)
        = cellFrequency (cells 0 + ∑ index : Fin (inner + 1), cells index.succ) := by
          rw [Fin.sum_univ_succ]
      _ ≤ cellFrequency (cells 0) +
          cellFrequency (∑ index : Fin (inner + 1), cells index.succ) :=
          cellFrequency_add_le _ _
      _ ≤ cellFrequency (cells 0) +
          ∑ index : Fin (inner + 1), cellFrequency (cells index.succ) := by linarith
      _ = ∑ index, cellFrequency (cells index) :=
          (Fin.sum_univ_succ (fun index => cellFrequency (cells index))).symm

theorem cellPolynomialWeight_tuple_le (smaller : ℕ) (cells : Fin (smaller + 1) → ℤ) :
    cellPolynomialWeight (∑ index, cells index) ≤
      ∑ index, cellPolynomialWeight (cells index) := by
  induction smaller with
  | zero =>
    simp
  | succ inner inductive_step =>
    have tail_le : cellPolynomialWeight (∑ index : Fin (inner + 1), cells index.succ) ≤
        ∑ index : Fin (inner + 1), cellPolynomialWeight (cells index.succ) :=
      inductive_step (fun index => cells index.succ)
    calc cellPolynomialWeight (∑ index, cells index)
        = cellPolynomialWeight (cells 0 + ∑ index : Fin (inner + 1), cells index.succ) := by
          rw [Fin.sum_univ_succ]
      _ ≤ cellPolynomialWeight (cells 0) +
          cellPolynomialWeight (∑ index : Fin (inner + 1), cells index.succ) :=
          cellPolynomialWeight_add_le _ _
      _ ≤ cellPolynomialWeight (cells 0) +
          ∑ index : Fin (inner + 1), cellPolynomialWeight (cells index.succ) := by linarith
      _ = ∑ index, cellPolynomialWeight (cells index) :=
          (Fin.sum_univ_succ (fun index => cellPolynomialWeight (cells index))).symm

/-- The one-high split of the full weight along a nonempty finite tuple of
cells: the exponential splits completely and the polynomial part lands on one
factor, with the arity power as the only constant. -/
theorem tameWeight_tuple_split (parameters : PhaseParameters) (grade : ℕ)
    {smaller : ℕ} (cells : Fin (smaller + 1) → ℤ) :
    tameWeight parameters grade (∑ index, cells index) ≤
      ((smaller + 1 : ℕ) : ℝ) ^ grade *
        ∑ index, tameWeight parameters grade (cells index) *
          ∏ other ∈ Finset.univ.erase index, tameWeight parameters 0 (cells other) := by
  have exponential_split :
      Real.exp (parameters.sigma0 * cellFrequency (∑ index, cells index)) ≤
        ∏ index, Real.exp (parameters.sigma0 * cellFrequency (cells index)) := by
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.mpr
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (cellFrequency_tuple_le smaller cells)
      parameters.sigma0_pos.le
  obtain ⟨top, _, top_maximal⟩ := Finset.exists_max_image Finset.univ
    (fun index => cellPolynomialWeight (cells index)) ⟨0, Finset.mem_univ _⟩
  have sum_le_card_mul : ∑ index, cellPolynomialWeight (cells index) ≤
      ((smaller + 1 : ℕ) : ℝ) * cellPolynomialWeight (cells top) := by
    have card_bound := Finset.sum_le_card_nsmul Finset.univ
      (fun index => cellPolynomialWeight (cells index))
      (cellPolynomialWeight (cells top)) (fun index _ => top_maximal index (Finset.mem_univ _))
    simpa [nsmul_eq_mul, Finset.card_univ] using card_bound
  have polynomial_power_split : cellPolynomialWeight (∑ index, cells index) ^ grade ≤
      ((smaller + 1 : ℕ) : ℝ) ^ grade * cellPolynomialWeight (cells top) ^ grade := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (cellPolynomialWeight_pos _).le
    exact (cellPolynomialWeight_tuple_le smaller cells).trans sum_le_card_mul
  have exponential_nonneg : (0 : ℝ) ≤ ∏ index, Real.exp
      (parameters.sigma0 * cellFrequency (cells index)) :=
    Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le)
  calc tameWeight parameters grade (∑ index, cells index)
      ≤ (∏ index, Real.exp (parameters.sigma0 * cellFrequency (cells index))) *
        (((smaller + 1 : ℕ) : ℝ) ^ grade * cellPolynomialWeight (cells top) ^ grade) := by
        apply mul_le_mul exponential_split polynomial_power_split
          (pow_nonneg (cellPolynomialWeight_pos _).le _) exponential_nonneg
    _ = ((smaller + 1 : ℕ) : ℝ) ^ grade * (tameWeight parameters grade (cells top) *
        ∏ other ∈ Finset.univ.erase top, tameWeight parameters 0 (cells other)) := by
        unfold tameWeight
        simp only [pow_zero, mul_one]
        rw [← Finset.mul_prod_erase Finset.univ
          (fun index => Real.exp (parameters.sigma0 * cellFrequency (cells index)))
          (Finset.mem_univ top)]
        ring
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) grade)
        apply Finset.single_le_sum
          (f := fun index => tameWeight parameters grade (cells index) *
            ∏ other ∈ Finset.univ.erase index, tameWeight parameters 0 (cells other))
          (fun index _ => mul_nonneg (tameWeight_pos _ _ _).le
            (Finset.prod_nonneg (fun _ _ => (tameWeight_pos _ _ _).le)))
          (Finset.mem_univ top)

/-- Grade-zero full splitting along a nonempty tuple, with no constant. -/
theorem tameWeight_zero_tuple_split (parameters : PhaseParameters)
    {smaller : ℕ} (cells : Fin (smaller + 1) → ℤ) :
    tameWeight parameters 0 (∑ index, cells index) ≤
      ∏ index, tameWeight parameters 0 (cells index) := by
  induction smaller with
  | zero =>
    simp
  | succ inner inductive_step =>
    have tail_le : tameWeight parameters 0 (∑ index : Fin (inner + 1), cells index.succ) ≤
        ∏ index : Fin (inner + 1), tameWeight parameters 0 (cells index.succ) :=
      inductive_step (fun index => cells index.succ)
    calc tameWeight parameters 0 (∑ index, cells index)
        = tameWeight parameters 0 (cells 0 + ∑ index : Fin (inner + 1), cells index.succ) := by
          rw [Fin.sum_univ_succ]
      _ ≤ tameWeight parameters 0 (cells 0) *
          tameWeight parameters 0 (∑ index : Fin (inner + 1), cells index.succ) :=
          tameWeight_zero_add_le parameters _ _
      _ ≤ tameWeight parameters 0 (cells 0) *
          ∏ index : Fin (inner + 1), tameWeight parameters 0 (cells index.succ) :=
          mul_le_mul_of_nonneg_left tail_le (tameWeight_pos _ _ _).le
      _ = ∏ index, tameWeight parameters 0 (cells index) :=
          (Fin.prod_univ_succ (fun index => tameWeight parameters 0 (cells index))).symm

/-! ### The nonnegative extended-real convolution core -/

/-- Splitting a tuple of cells into its first entry and its tail. -/
def tameSplitFirstEquiv (arity : ℕ) : (Fin (arity + 1) → ℤ) ≃ (ℤ × (Fin arity → ℤ)) where
  toFun cells := (cells 0, Fin.tail cells)
  invFun pair := Fin.cons pair.1 pair.2
  left_inv cells := Fin.cons_self_tail cells
  right_inv pair := by
    refine Prod.ext ?_ ?_ <;> simp

/-- The iterated cell convolution of a finite tuple of nonnegative
extended-real families; the empty product is the unit at the zero cell. -/
noncomputable def tupleConvolutionENN : (arity : ℕ) → (Fin arity → ℤ → ℝ≥0∞) → ℤ → ℝ≥0∞
  | 0, _, cell => if cell = 0 then 1 else 0
  | arity + 1, factors, cell =>
      ∑' shift, factors 0 shift * tupleConvolutionENN arity (Fin.tail factors) (cell - shift)

/-- Every weighted total of an iterated convolution is the free tuple sum. -/
theorem tupleConvolutionENN_weighted (weightFamily : ℤ → ℝ≥0∞) :
    ∀ (arity : ℕ) (factors : Fin arity → ℤ → ℝ≥0∞),
    ∑' cell, weightFamily cell * tupleConvolutionENN arity factors cell =
      ∑' cells : Fin arity → ℤ,
        weightFamily (∑ index, cells index) * ∏ index, factors index (cells index) := by
  intro arity
  induction arity generalizing weightFamily with
  | zero =>
    intro factors
    rw [tsum_eq_single (0 : ℤ) (by
      intro cell nonzero
      simp [tupleConvolutionENN, nonzero])]
    rw [tsum_eq_single (fun index : Fin 0 => 0) (by
      intro cells distinct
      exact absurd (funext (fun index => index.elim0)) distinct)]
    simp [tupleConvolutionENN]
  | succ smaller inductive_step =>
    intro factors
    calc ∑' cell, weightFamily cell * tupleConvolutionENN (smaller + 1) factors cell
        = ∑' cell, ∑' shift, weightFamily cell * (factors 0 shift *
            tupleConvolutionENN smaller (Fin.tail factors) (cell - shift)) := by
          apply tsum_congr
          intro cell
          rw [tupleConvolutionENN, ENNReal.tsum_mul_left]
      _ = ∑' shift, ∑' cell, weightFamily cell * (factors 0 shift *
            tupleConvolutionENN smaller (Fin.tail factors) (cell - shift)) :=
          ENNReal.tsum_comm
      _ = ∑' shift, ∑' rest, weightFamily (shift + rest) * (factors 0 shift *
            tupleConvolutionENN smaller (Fin.tail factors) rest) := by
          apply tsum_congr
          intro shift
          calc ∑' cell, weightFamily cell * (factors 0 shift *
                tupleConvolutionENN smaller (Fin.tail factors) (cell - shift))
              = ∑' cell, (fun rest => weightFamily (shift + rest) * (factors 0 shift *
                  tupleConvolutionENN smaller (Fin.tail factors) rest))
                  (Grad.NonlinearProduct.cellShiftEquiv shift cell) := by
                apply tsum_congr
                intro cell
                have recover : shift + (cell - shift) = cell := by ring
                simp only [Grad.NonlinearProduct.cellShiftEquiv, Equiv.coe_fn_mk, recover]
            _ = _ := (Grad.NonlinearProduct.cellShiftEquiv shift).tsum_eq
                  (fun rest => weightFamily (shift + rest) * (factors 0 shift *
                    tupleConvolutionENN smaller (Fin.tail factors) rest))
      _ = ∑' shift, factors 0 shift * ∑' rest, weightFamily (shift + rest) *
            tupleConvolutionENN smaller (Fin.tail factors) rest := by
          apply tsum_congr
          intro shift
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro rest
          ring
      _ = ∑' shift, factors 0 shift * ∑' cells : Fin smaller → ℤ,
            weightFamily (shift + ∑ index, cells index) *
              ∏ index, Fin.tail factors index (cells index) := by
          apply tsum_congr
          intro shift
          rw [inductive_step (fun rest => weightFamily (shift + rest)) (Fin.tail factors)]
      _ = ∑' shift, ∑' cells : Fin smaller → ℤ,
            weightFamily (shift + ∑ index, cells index) * (factors 0 shift *
              ∏ index, Fin.tail factors index (cells index)) := by
          apply tsum_congr
          intro shift
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro cells
          ring
      _ = ∑' pair : ℤ × (Fin smaller → ℤ),
            weightFamily (pair.1 + ∑ index, pair.2 index) * (factors 0 pair.1 *
              ∏ index, Fin.tail factors index (pair.2 index)) :=
          (ENNReal.tsum_prod' (f := fun pair : ℤ × (Fin smaller → ℤ) =>
            weightFamily (pair.1 + ∑ index, pair.2 index) * (factors 0 pair.1 *
              ∏ index, Fin.tail factors index (pair.2 index)))).symm
      _ = _ := by
          rw [← ((tameSplitFirstEquiv smaller).tsum_eq
            (fun pair : ℤ × (Fin smaller → ℤ) =>
              weightFamily (pair.1 + ∑ index, pair.2 index) * (factors 0 pair.1 *
                ∏ index, Fin.tail factors index (pair.2 index))))]
          apply tsum_congr
          intro cells
          simp only [tameSplitFirstEquiv, Equiv.coe_fn_mk]
          rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
          rfl

/-- The free tuple total of a pure product factorizes into single totals. -/
theorem tupleENN_product_factorizes :
    ∀ (arity : ℕ) (factors : Fin arity → ℤ → ℝ≥0∞),
    ∑' cells : Fin arity → ℤ, ∏ index, factors index (cells index) =
      ∏ index, ∑' shift, factors index shift := by
  intro arity
  induction arity with
  | zero =>
    intro factors
    rw [tsum_eq_single (fun index : Fin 0 => 0) (by
      intro cells distinct
      exact absurd (funext (fun index => index.elim0)) distinct)]
    simp
  | succ smaller inductive_step =>
    intro factors
    calc ∑' cells : Fin (smaller + 1) → ℤ, ∏ index, factors index (cells index)
        = ∑' cells : Fin (smaller + 1) → ℤ, factors 0 (cells 0) *
            ∏ index, Fin.tail factors index (Fin.tail cells index) := by
          apply tsum_congr
          intro cells
          rw [Fin.prod_univ_succ]
          rfl
      _ = ∑' pair : ℤ × (Fin smaller → ℤ), factors 0 pair.1 *
            ∏ index, Fin.tail factors index (pair.2 index) := by
          rw [← ((tameSplitFirstEquiv smaller).tsum_eq
            (fun pair : ℤ × (Fin smaller → ℤ) => factors 0 pair.1 *
              ∏ index, Fin.tail factors index (pair.2 index)))]
          apply tsum_congr
          intro cells
          simp only [tameSplitFirstEquiv, Equiv.coe_fn_mk]
      _ = ∑' shift, ∑' cells : Fin smaller → ℤ, factors 0 shift *
            ∏ index, Fin.tail factors index (cells index) :=
          ENNReal.tsum_prod'
      _ = (∑' shift, factors 0 shift) * ∑' cells : Fin smaller → ℤ,
            ∏ index, Fin.tail factors index (cells index) := by
          rw [← ENNReal.tsum_mul_right]
          apply tsum_congr
          intro shift
          rw [ENNReal.tsum_mul_left]
      _ = _ := by
          rw [inductive_step (Fin.tail factors), Fin.prod_univ_succ]
          rfl

/-- The extended-real envelope of a nonnegative family at one grade. -/
def tameEnvelopeENN (parameters : PhaseParameters) (grade : ℕ) (family : ℤ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' cell, ENNReal.ofReal (tameWeight parameters grade cell) * family cell

/-- One split factor family: the graded weight at the distinguished index and
the zero-grade weight elsewhere. -/
def tameSplitFamily (parameters : PhaseParameters) (grade : ℕ) {arity : ℕ}
    (factors : Fin arity → ℤ → ℝ≥0∞) (index position : Fin arity) (cell : ℤ) : ℝ≥0∞ :=
  if position = index then
    ENNReal.ofReal (tameWeight parameters grade cell) * factors position cell
  else ENNReal.ofReal (tameWeight parameters 0 cell) * factors position cell

theorem tameSplitFamily_total (parameters : PhaseParameters) (grade : ℕ) {arity : ℕ}
    (factors : Fin arity → ℤ → ℝ≥0∞) (index : Fin arity) :
    ∑' cells : Fin arity → ℤ,
        ∏ position, tameSplitFamily parameters grade factors index position (cells position) =
      tameEnvelopeENN parameters grade (factors index) *
        ∏ other ∈ Finset.univ.erase index, tameEnvelopeENN parameters 0 (factors other) := by
  rw [tupleENN_product_factorizes arity (tameSplitFamily parameters grade factors index)]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun position => ∑' shift, tameSplitFamily parameters grade factors index position shift)
    (Finset.mem_univ index)]
  congr 1
  · apply tsum_congr
    intro shift
    rw [tameSplitFamily, if_pos rfl]
  · apply Finset.prod_congr rfl
    intro other membership
    apply tsum_congr
    intro shift
    rw [tameSplitFamily, if_neg (Finset.ne_of_mem_erase membership)]

/-- The extended-real master estimate: the graded envelope of an iterated
convolution of a nonempty tuple has the exact Q6 one-high form with the
arity-power constant. -/
theorem tupleConvolutionENN_envelope_le (parameters : PhaseParameters) (grade : ℕ)
    {smaller : ℕ} (factors : Fin (smaller + 1) → ℤ → ℝ≥0∞) :
    tameEnvelopeENN parameters grade (tupleConvolutionENN (smaller + 1) factors) ≤
      ((smaller + 1 : ℕ) : ℝ≥0∞) ^ grade *
        ∑ index, tameEnvelopeENN parameters grade (factors index) *
          ∏ other ∈ Finset.univ.erase index, tameEnvelopeENN parameters 0 (factors other) := by
  rw [tameEnvelopeENN, tupleConvolutionENN_weighted]
  have pointwise (cells : Fin (smaller + 1) → ℤ) :
      ENNReal.ofReal (tameWeight parameters grade (∑ index, cells index)) *
        ∏ index, factors index (cells index) ≤
      ((smaller + 1 : ℕ) : ℝ≥0∞) ^ grade * ∑ index,
        ∏ position, tameSplitFamily parameters grade factors index position (cells position) := by
    have product_form (index : Fin (smaller + 1)) :
        ∏ position, tameSplitFamily parameters grade factors index position (cells position) =
        (ENNReal.ofReal (tameWeight parameters grade (cells index)) *
          ∏ other ∈ Finset.univ.erase index,
            ENNReal.ofReal (tameWeight parameters 0 (cells other))) *
          ∏ position, factors position (cells position) := by
      rw [← Finset.mul_prod_erase Finset.univ
        (fun position => tameSplitFamily parameters grade factors index position (cells position))
        (Finset.mem_univ index)]
      rw [tameSplitFamily, if_pos rfl]
      rw [← Finset.mul_prod_erase Finset.univ
        (fun position => factors position (cells position)) (Finset.mem_univ index)]
      have erased : ∏ other ∈ Finset.univ.erase index,
          tameSplitFamily parameters grade factors index other (cells other) =
          ∏ other ∈ Finset.univ.erase index,
            (ENNReal.ofReal (tameWeight parameters 0 (cells other)) * factors other (cells other)) := by
        apply Finset.prod_congr rfl
        intro other membership
        rw [tameSplitFamily, if_neg (Finset.ne_of_mem_erase membership)]
      rw [erased, Finset.prod_mul_distrib]
      ring
    have weight_le := tameWeight_tuple_split parameters grade cells
    calc ENNReal.ofReal (tameWeight parameters grade (∑ index, cells index)) *
          ∏ index, factors index (cells index)
        ≤ ENNReal.ofReal (((smaller + 1 : ℕ) : ℝ) ^ grade *
            ∑ index, tameWeight parameters grade (cells index) *
              ∏ other ∈ Finset.univ.erase index, tameWeight parameters 0 (cells other)) *
          ∏ index, factors index (cells index) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal weight_le) le_rfl
      _ = ((smaller + 1 : ℕ) : ℝ≥0∞) ^ grade * ∑ index,
            (ENNReal.ofReal (tameWeight parameters grade (cells index)) *
              ∏ other ∈ Finset.univ.erase index,
                ENNReal.ofReal (tameWeight parameters 0 (cells other))) *
            ∏ position, factors position (cells position) := by
          rw [ENNReal.ofReal_mul (pow_nonneg (Nat.cast_nonneg _) grade),
            ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
            ENNReal.ofReal_sum_of_nonneg (fun index _ => mul_nonneg (tameWeight_pos _ _ _).le
              (Finset.prod_nonneg (fun _ _ => (tameWeight_pos _ _ _).le))),
            mul_assoc, Finset.sum_mul]
          congr 2
          funext index
          rw [ENNReal.ofReal_mul (tameWeight_pos _ _ _).le,
            ENNReal.ofReal_prod_of_nonneg (fun _ _ => (tameWeight_pos _ _ _).le)]
      _ = _ := by
          congr 1
          apply Finset.sum_congr rfl
          intro index _
          rw [product_form index]
  calc ∑' cells : Fin (smaller + 1) → ℤ,
        ENNReal.ofReal (tameWeight parameters grade (∑ index, cells index)) *
          ∏ index, factors index (cells index)
      ≤ ∑' cells : Fin (smaller + 1) → ℤ, ((smaller + 1 : ℕ) : ℝ≥0∞) ^ grade * ∑ index,
          ∏ position, tameSplitFamily parameters grade factors index position (cells position) :=
        ENNReal.tsum_le_tsum pointwise
    _ = ((smaller + 1 : ℕ) : ℝ≥0∞) ^ grade * ∑ index, ∑' cells : Fin (smaller + 1) → ℤ,
          ∏ position, tameSplitFamily parameters grade factors index position (cells position) := by
        rw [ENNReal.tsum_mul_left]
        congr 1
        exact Summable.tsum_finsetSum (fun index _ => ENNReal.summable)
    _ = _ :=
        congrArg (fun total => ((smaller + 1 : ℕ) : ℝ≥0∞) ^ grade * total)
          (Finset.sum_congr rfl
            (fun index _ => tameSplitFamily_total parameters grade factors index))

/-- The sharp grade-zero estimate for nonempty tuples: the zero-grade envelope
of an iterated convolution is at most the product of the zero-grade envelopes. -/
theorem tupleConvolutionENN_envelope_zero_le (parameters : PhaseParameters)
    {smaller : ℕ} (factors : Fin (smaller + 1) → ℤ → ℝ≥0∞) :
    tameEnvelopeENN parameters 0 (tupleConvolutionENN (smaller + 1) factors) ≤
      ∏ index, tameEnvelopeENN parameters 0 (factors index) := by
  rw [tameEnvelopeENN, tupleConvolutionENN_weighted]
  have pointwise (cells : Fin (smaller + 1) → ℤ) :
      ENNReal.ofReal (tameWeight parameters 0 (∑ index, cells index)) *
        ∏ index, factors index (cells index) ≤
      ∏ index, (ENNReal.ofReal (tameWeight parameters 0 (cells index)) *
        factors index (cells index)) := by
    rw [Finset.prod_mul_distrib]
    apply mul_le_mul' _ le_rfl
    calc ENNReal.ofReal (tameWeight parameters 0 (∑ index, cells index))
        ≤ ENNReal.ofReal (∏ index, tameWeight parameters 0 (cells index)) :=
          ENNReal.ofReal_le_ofReal (tameWeight_zero_tuple_split parameters cells)
      _ = _ := ENNReal.ofReal_prod_of_nonneg (fun _ _ => (tameWeight_pos _ _ _).le)
  calc ∑' cells : Fin (smaller + 1) → ℤ,
        ENNReal.ofReal (tameWeight parameters 0 (∑ index, cells index)) *
          ∏ index, factors index (cells index)
      ≤ ∑' cells : Fin (smaller + 1) → ℤ, ∏ index,
          (ENNReal.ofReal (tameWeight parameters 0 (cells index)) * factors index (cells index)) :=
        ENNReal.tsum_le_tsum pointwise
    _ = _ :=
        tupleENN_product_factorizes (smaller + 1)
          (fun index cell => ENNReal.ofReal (tameWeight parameters 0 cell) * factors index cell)

end Grad.NonlinearQuotientBounds
