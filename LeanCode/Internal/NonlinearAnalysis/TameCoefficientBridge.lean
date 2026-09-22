import TameCoefficientAlgebra

noncomputable section

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! Real Q5 envelopes for complex coefficient families, the raw binary cell
convolution, and the bridge between the real envelopes and the extended-real
convolution core.  Everything here is stated for raw families; the algebra
subtype is built on top of these lemmas. -/

/-- One real envelope summand `e^{σ₀ λ} μ^s ‖c_cell‖` of the Q5 norm. -/
def tameEnvelopeTerm (parameters : PhaseParameters) (grade : ℕ) (c : ℤ → ℂ) (cell : ℤ) : ℝ :=
  tameWeight parameters grade cell * ‖c cell‖

/-- All-grade finiteness of the Q5 norms: the coefficient-core property. -/
def TameSummableFamily (parameters : PhaseParameters) (c : ℤ → ℂ) : Prop :=
  ∀ grade : ℕ, Summable (tameEnvelopeTerm parameters grade c)

/-- The real Q5 envelope at one grade. -/
def tameEnvelope (parameters : PhaseParameters) (grade : ℕ) (c : ℤ → ℂ) : ℝ :=
  ∑' cell, tameEnvelopeTerm parameters grade c cell

theorem tameEnvelopeTerm_nonneg (parameters : PhaseParameters) (grade : ℕ)
    (c : ℤ → ℂ) (cell : ℤ) : 0 ≤ tameEnvelopeTerm parameters grade c cell :=
  mul_nonneg (tameWeight_pos parameters grade cell).le (norm_nonneg _)

theorem tameEnvelope_nonneg (parameters : PhaseParameters) (grade : ℕ) (c : ℤ → ℂ) :
    0 ≤ tameEnvelope parameters grade c :=
  tsum_nonneg (tameEnvelopeTerm_nonneg parameters grade c)

theorem norm_le_tameEnvelopeTerm (parameters : PhaseParameters) (grade : ℕ)
    (c : ℤ → ℂ) (cell : ℤ) : ‖c cell‖ ≤ tameEnvelopeTerm parameters grade c cell := by
  calc ‖c cell‖ = 1 * ‖c cell‖ := (one_mul _).symm
  _ ≤ _ := mul_le_mul_of_nonneg_right (tameWeight_one_le parameters grade cell) (norm_nonneg _)

theorem tameEnvelopeTerm_mono (parameters : PhaseParameters) {lower upper : ℕ}
    (gradeLe : lower ≤ upper) (c : ℤ → ℂ) (cell : ℤ) :
    tameEnvelopeTerm parameters lower c cell ≤ tameEnvelopeTerm parameters upper c cell :=
  mul_le_mul_of_nonneg_right (tameWeight_mono parameters gradeLe cell) (norm_nonneg _)

theorem TameSummableFamily.norm_summable {parameters : PhaseParameters} {c : ℤ → ℂ}
    (summable : TameSummableFamily parameters c) : Summable (fun cell => ‖c cell‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_le_tameEnvelopeTerm parameters 0 c) (summable 0)

theorem norm_le_tameEnvelope {parameters : PhaseParameters} {c : ℤ → ℂ}
    (summable : TameSummableFamily parameters c) (grade : ℕ) (cell : ℤ) :
    ‖c cell‖ ≤ tameEnvelope parameters grade c :=
  (norm_le_tameEnvelopeTerm parameters grade c cell).trans
    ((summable grade).le_tsum cell
      (fun other _ => tameEnvelopeTerm_nonneg parameters grade c other))

theorem tameEnvelope_mono {parameters : PhaseParameters} {c : ℤ → ℂ}
    (summable : TameSummableFamily parameters c) {lower upper : ℕ} (gradeLe : lower ≤ upper) :
    tameEnvelope parameters lower c ≤ tameEnvelope parameters upper c :=
  (summable lower).tsum_le_tsum (tameEnvelopeTerm_mono parameters gradeLe c) (summable upper)

/-! ### Real–extended-real bridging -/

theorem summable_of_ofReal_tsum_ne_top {Index : Type} {f : Index → ℝ}
    (nonneg : ∀ index, 0 ≤ f index)
    (finite : (∑' index, ENNReal.ofReal (f index)) ≠ ⊤) : Summable f := by
  have coeForm : (fun index => ((Real.toNNReal (f index) : ℝ≥0) : ℝ≥0∞)) =
      fun index => ENNReal.ofReal (f index) := rfl
  have nnSummable : Summable (fun index => Real.toNNReal (f index)) := by
    apply ENNReal.tsum_coe_ne_top_iff_summable.mp
    rw [coeForm]
    exact finite
  have realSummable : Summable (fun index => ((Real.toNNReal (f index) : ℝ≥0) : ℝ)) :=
    NNReal.summable_coe.mpr nnSummable
  apply realSummable.congr
  intro index
  exact Real.coe_toNNReal (f index) (nonneg index)

theorem ofReal_tsum_ne_top_of_summable {Index : Type} {f : Index → ℝ}
    (nonneg : ∀ index, 0 ≤ f index) (summable : Summable f) :
    (∑' index, ENNReal.ofReal (f index)) ≠ ⊤ := by
  have coeForm : (fun index => ENNReal.ofReal (f index)) =
      fun index => ((Real.toNNReal (f index) : ℝ≥0) : ℝ≥0∞) := rfl
  rw [coeForm]
  apply ENNReal.tsum_coe_ne_top_iff_summable.mpr
  have nnSummable : Summable (fun index => Real.toNNReal (f index)) := by
    apply NNReal.summable_coe.mp
    apply summable.congr
    intro index
    exact (Real.coe_toNNReal (f index) (nonneg index)).symm
  exact nnSummable

theorem ofReal_tsum_eq_tsum_ofReal {Index : Type} {f : Index → ℝ}
    (nonneg : ∀ index, 0 ≤ f index) (summable : Summable f) :
    ENNReal.ofReal (∑' index, f index) = ∑' index, ENNReal.ofReal (f index) :=
  ENNReal.ofReal_tsum_of_nonneg nonneg summable

/-- The extended-real norm family of a complex coefficient family. -/
def tameNormENN (c : ℤ → ℂ) (cell : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal ‖c cell‖

theorem tameEnvelopeENN_normENN_eq {parameters : PhaseParameters} {c : ℤ → ℂ}
    (summable : TameSummableFamily parameters c) (grade : ℕ) :
    tameEnvelopeENN parameters grade (tameNormENN c) =
      ENNReal.ofReal (tameEnvelope parameters grade c) := by
  rw [tameEnvelope,
    ofReal_tsum_eq_tsum_ofReal (tameEnvelopeTerm_nonneg parameters grade c) (summable grade)]
  apply tsum_congr
  intro cell
  rw [tameEnvelopeTerm, ENNReal.ofReal_mul (tameWeight_pos parameters grade cell).le]
  rfl

theorem tameEnvelopeENN_normENN_ne_top {parameters : PhaseParameters} {c : ℤ → ℂ}
    (summable : TameSummableFamily parameters c) (grade : ℕ) :
    tameEnvelopeENN parameters grade (tameNormENN c) ≠ ⊤ := by
  rw [tameEnvelopeENN_normENN_eq summable grade]
  exact ENNReal.ofReal_ne_top

/-! ### The raw binary convolution and its extended-real domination -/

/-- The raw binary cell convolution of two complex coefficient families. -/
def rawConvolution (c d : ℤ → ℂ) (cell : ℤ) : ℂ :=
  ∑' shift, c shift * d (cell - shift)

/-- The extended-real binary convolution of the norm families. -/
def rawConvolutionENN (c d : ℤ → ℂ) (cell : ℤ) : ℝ≥0∞ :=
  ∑' shift, tameNormENN c shift * tameNormENN d (cell - shift)

/-- Pointwise domination of the raw convolution by the extended-real
convolution of the norm families, with no summability hypothesis. -/
theorem rawConvolution_normENN_le (c d : ℤ → ℂ) (cell : ℤ) :
    tameNormENN (rawConvolution c d) cell ≤ rawConvolutionENN c d cell := by
  by_cases summable : Summable (fun shift => ‖c shift‖ * ‖d (cell - shift)‖)
  · have valueSummable : Summable (fun shift => c shift * d (cell - shift)) := by
      apply Summable.of_norm
      apply summable.congr
      intro shift
      rw [norm_mul]
    have norm_le : ‖rawConvolution c d cell‖ ≤ ∑' shift, ‖c shift‖ * ‖d (cell - shift)‖ := by
      apply (norm_tsum_le_tsum_norm valueSummable.norm).trans_eq
      apply tsum_congr
      intro shift
      rw [norm_mul]
    calc tameNormENN (rawConvolution c d) cell
        ≤ ENNReal.ofReal (∑' shift, ‖c shift‖ * ‖d (cell - shift)‖) :=
          ENNReal.ofReal_le_ofReal norm_le
      _ = ∑' shift, ENNReal.ofReal (‖c shift‖ * ‖d (cell - shift)‖) :=
          ofReal_tsum_eq_tsum_ofReal
            (fun shift => mul_nonneg (norm_nonneg _) (norm_nonneg _)) summable
      _ = _ := by
          apply tsum_congr
          intro shift
          rw [ENNReal.ofReal_mul (norm_nonneg _)]
          rfl
  · have top : rawConvolutionENN c d cell = ⊤ := by
      by_contra nontop
      apply summable
      have := summable_of_ofReal_tsum_ne_top
        (f := fun shift => ‖c shift‖ * ‖d (cell - shift)‖)
        (fun shift => mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
      · exact this
      · intro isTop
        apply nontop
        rw [rawConvolutionENN, ← isTop]
        apply tsum_congr
        intro shift
        rw [ENNReal.ofReal_mul (norm_nonneg _)]
        rfl
    rw [top]
    exact le_top

/-- The single-factor iterated convolution is the factor itself. -/
theorem tupleConvolutionENN_single (factors : Fin 1 → ℤ → ℝ≥0∞) (cell : ℤ) :
    tupleConvolutionENN 1 factors cell = factors 0 cell := by
  rw [tupleConvolutionENN]
  rw [tsum_eq_single cell (by
    intro shift distinct
    have nonzero : cell - shift ≠ 0 := fun zero => distinct (by omega)
    rw [tupleConvolutionENN, if_neg nonzero, mul_zero])]
  rw [tupleConvolutionENN, if_pos (sub_self cell), mul_one]

/-- The two-factor iterated convolution is the binary convolution of the
norm families. -/
theorem tupleConvolutionENN_pair (c d : ℤ → ℂ) (cell : ℤ) :
    tupleConvolutionENN 2 ![tameNormENN c, tameNormENN d] cell =
      rawConvolutionENN c d cell := by
  rw [tupleConvolutionENN]
  apply tsum_congr
  intro shift
  congr 1
  exact tupleConvolutionENN_single _ (cell - shift)

/-- Monotonicity of the extended-real convolution in the tail family. -/
theorem rawConvolutionENN_mono_right {first second : ℤ → ℝ≥0∞}
    (head : ℤ → ℝ≥0∞) (le : ∀ cell, first cell ≤ second cell) (cell : ℤ) :
    ∑' shift, head shift * first (cell - shift) ≤
      ∑' shift, head shift * second (cell - shift) :=
  ENNReal.tsum_le_tsum (fun shift => mul_le_mul' le_rfl (le (cell - shift)))

/-! ### Closure of the coefficient core under the binary convolution -/

theorem rawConvolution_term_summable {parameters : PhaseParameters} {c d : ℤ → ℂ}
    (cSummable : TameSummableFamily parameters c)
    (dSummable : TameSummableFamily parameters d) (cell : ℤ) :
    Summable (fun shift => c shift * d (cell - shift)) := by
  apply Summable.of_norm
  have bound (shift : ℤ) : ‖c shift * d (cell - shift)‖ ≤
      tameEnvelope parameters 0 d * ‖c shift‖ := by
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_le_tameEnvelope dSummable 0 (cell - shift))
      (norm_nonneg _)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) bound
    (cSummable.norm_summable.mul_left _)

/-- The binary convolution of two coefficient-core families is again in the
coefficient core, with the exact binary one-high envelope bound and the sharp
grade-zero bound. -/
theorem rawConvolution_summable_family {parameters : PhaseParameters} {c d : ℤ → ℂ}
    (cSummable : TameSummableFamily parameters c)
    (dSummable : TameSummableFamily parameters d) :
    TameSummableFamily parameters (rawConvolution c d) := by
  intro grade
  apply summable_of_ofReal_tsum_ne_top (tameEnvelopeTerm_nonneg parameters grade _)
  have pointwise (cell : ℤ) : ENNReal.ofReal (tameEnvelopeTerm parameters grade
      (rawConvolution c d) cell) ≤
      ENNReal.ofReal (tameWeight parameters grade cell) *
        tupleConvolutionENN 2 ![tameNormENN c, tameNormENN d] cell := by
    rw [tameEnvelopeTerm, ENNReal.ofReal_mul (tameWeight_pos parameters grade cell).le,
      tupleConvolutionENN_pair]
    exact mul_le_mul' le_rfl (rawConvolution_normENN_le c d cell)
  apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum pointwise)
  apply ne_top_of_le_ne_top _
    (tupleConvolutionENN_envelope_le parameters grade ![tameNormENN c, tameNormENN d])
  apply ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
  apply (ENNReal.sum_lt_top.mpr _).ne
  intro index _
  apply ENNReal.mul_lt_top
  · fin_cases index
    · exact (tameEnvelopeENN_normENN_ne_top cSummable grade).lt_top
    · exact (tameEnvelopeENN_normENN_ne_top dSummable grade).lt_top
  · apply ENNReal.prod_lt_top
    intro other _
    fin_cases other
    · exact (tameEnvelopeENN_normENN_ne_top cSummable 0).lt_top
    · exact (tameEnvelopeENN_normENN_ne_top dSummable 0).lt_top

end Grad.NonlinearQuotientBounds
