import TameCoefficientRing

noncomputable section

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! The exact Q6 one-high envelope estimates for products in the coefficient
algebra, specialized to ring powers, together with the elementary envelope
laws used by the root series. -/

variable {parameters : PhaseParameters}

/-- The envelope of a coefficient-core element at one grade. -/
def coefficientEnvelope (grade : ℕ) (c : TameCoefficient parameters) : ℝ :=
  tameEnvelope parameters grade c.val

theorem coefficientEnvelope_nonneg (grade : ℕ) (c : TameCoefficient parameters) :
    0 ≤ coefficientEnvelope grade c :=
  tameEnvelope_nonneg parameters grade c.val

theorem coefficientEnvelope_mono {lower upper : ℕ} (gradeLe : lower ≤ upper)
    (c : TameCoefficient parameters) :
    coefficientEnvelope lower c ≤ coefficientEnvelope upper c :=
  tameEnvelope_mono c.property gradeLe

theorem coefficientEnvelope_smul (grade : ℕ) (scalar : ℂ) (c : TameCoefficient parameters) :
    coefficientEnvelope grade (scalar • c) = ‖scalar‖ * coefficientEnvelope grade c := by
  rw [coefficientEnvelope, coefficientEnvelope, tameEnvelope, tameEnvelope, ← tsum_mul_left]
  apply tsum_congr
  intro cell
  rw [tameSmul_val, tameEnvelopeTerm, tameEnvelopeTerm, Pi.smul_apply, norm_smul]
  ring

theorem coefficientEnvelope_add_le (grade : ℕ) (c d : TameCoefficient parameters) :
    coefficientEnvelope grade (c + d) ≤
      coefficientEnvelope grade c + coefficientEnvelope grade d := by
  rw [coefficientEnvelope, coefficientEnvelope, coefficientEnvelope, tameEnvelope,
    tameEnvelope, tameEnvelope,
    ← (c.property grade).tsum_add (d.property grade)]
  apply ((c + d).property grade).tsum_le_tsum _ ((c.property grade).add (d.property grade))
  intro cell
  rw [tameAdd_val, tameEnvelopeTerm]
  calc tameWeight parameters grade cell * ‖(c.val + d.val) cell‖
      ≤ tameWeight parameters grade cell * (‖c.val cell‖ + ‖d.val cell‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (tameWeight_pos _ _ _).le
    _ = tameEnvelopeTerm parameters grade c.val cell +
        tameEnvelopeTerm parameters grade d.val cell := by
        rw [tameEnvelopeTerm, tameEnvelopeTerm]
        ring

theorem coefficientEnvelope_neg (grade : ℕ) (c : TameCoefficient parameters) :
    coefficientEnvelope grade (-c) = coefficientEnvelope grade c := by
  rw [coefficientEnvelope, coefficientEnvelope, tameEnvelope, tameEnvelope]
  apply tsum_congr
  intro cell
  rw [tameEnvelopeTerm, tameEnvelopeTerm]
  congr 1
  calc ‖(-c).val cell‖ = ‖-(c.val cell)‖ := rfl
    _ = ‖c.val cell‖ := norm_neg _

theorem coefficientEnvelope_sub_le (grade : ℕ) (c d : TameCoefficient parameters) :
    coefficientEnvelope grade (c - d) ≤
      coefficientEnvelope grade c + coefficientEnvelope grade d := by
  rw [sub_eq_add_neg]
  exact (coefficientEnvelope_add_le grade c (-d)).trans_eq
    (by rw [coefficientEnvelope_neg])

theorem coefficientEnvelope_one (grade : ℕ) :
    coefficientEnvelope grade (1 : TameCoefficient parameters) =
      Real.exp parameters.sigma0 := by
  rw [coefficientEnvelope, tameEnvelope]
  rw [tsum_eq_single (0 : ℤ) (by
    intro cell nonzero
    rw [tameEnvelopeTerm, tameOne_val, tameDelta]
    simp [nonzero])]
  rw [tameEnvelopeTerm, tameOne_val, tameDelta, if_pos rfl, tameWeight]
  have frequency : cellFrequency (0 : ℤ) = 1 := by
    rw [cellFrequency, Grad.CellWeights.cellWeight]
    norm_num
  have polynomial : cellPolynomialWeight (0 : ℤ) = 1 := by
    rw [cellPolynomialWeight]
    norm_num
  rw [frequency, polynomial, one_pow, mul_one, mul_one, norm_one, mul_one]

/-! ### Domination of ring products by the extended-real convolution core -/

theorem tameProd_norm_dominated :
    ∀ (arity : ℕ) (factors : Fin arity → TameCoefficient parameters) (cell : ℤ),
    tameNormENN (∏ index, factors index).val cell ≤
      tupleConvolutionENN arity (fun index => tameNormENN (factors index).val) cell := by
  intro arity
  induction arity with
  | zero =>
    intro factors cell
    have empty : (∏ index, factors index) = (1 : TameCoefficient parameters) := by
      rw [Finset.univ_eq_empty, Finset.prod_empty]
    rw [empty, tupleConvolutionENN]
    by_cases zeroCell : cell = 0
    · subst zeroCell
      rw [if_pos rfl, tameNormENN, tameOne_val, tameDelta]
      simp
    · rw [if_neg zeroCell, tameNormENN, tameOne_val, tameDelta]
      simp [zeroCell]
  | succ smaller inductive_step =>
    intro factors cell
    have split : (∏ index, factors index) =
        factors 0 * ∏ index : Fin smaller, factors index.succ :=
      Fin.prod_univ_succ factors
    calc tameNormENN (∏ index, factors index).val cell
        = tameNormENN (rawConvolution (factors 0).val
            (∏ index : Fin smaller, factors index.succ).val) cell := by
          rw [split, tameMul_val]
      _ ≤ rawConvolutionENN (factors 0).val
            (∏ index : Fin smaller, factors index.succ).val cell :=
          rawConvolution_normENN_le _ _ cell
      _ ≤ ∑' shift, tameNormENN (factors 0).val shift *
            tupleConvolutionENN smaller
              (fun index => tameNormENN (factors index.succ).val) (cell - shift) :=
          rawConvolutionENN_mono_right _ (inductive_step (fun index => factors index.succ)) cell
      _ = _ := by
          rw [tupleConvolutionENN]
          rfl

theorem tameEnvelopeENN_mono_family {first second : ℤ → ℝ≥0∞} (grade : ℕ)
    (le : ∀ cell, first cell ≤ second cell) :
    tameEnvelopeENN parameters grade first ≤ tameEnvelopeENN parameters grade second :=
  ENNReal.tsum_le_tsum (fun cell => mul_le_mul' le_rfl (le cell))

/-- The real Q6 master estimate for nonempty ring products: the graded
envelope has the one-high form with the arity-power constant. -/
theorem tameProd_envelope_le (grade : ℕ) {smaller : ℕ}
    (factors : Fin (smaller + 1) → TameCoefficient parameters) :
    coefficientEnvelope grade (∏ index, factors index) ≤
      ((smaller + 1 : ℕ) : ℝ) ^ grade *
        ∑ index, coefficientEnvelope grade (factors index) *
          ∏ other ∈ Finset.univ.erase index, coefficientEnvelope 0 (factors other) := by
  have rightNonneg : 0 ≤ ((smaller + 1 : ℕ) : ℝ) ^ grade *
      ∑ index, coefficientEnvelope grade (factors index) *
        ∏ other ∈ Finset.univ.erase index, coefficientEnvelope 0 (factors other) := by
    apply mul_nonneg (pow_nonneg (Nat.cast_nonneg _) grade)
    apply Finset.sum_nonneg
    intro index _
    exact mul_nonneg (coefficientEnvelope_nonneg _ _)
      (Finset.prod_nonneg (fun _ _ => coefficientEnvelope_nonneg _ _))
  rw [← ENNReal.ofReal_le_ofReal_iff rightNonneg, coefficientEnvelope,
    ← tameEnvelopeENN_normENN_eq (∏ index, factors index).property grade]
  calc tameEnvelopeENN parameters grade (tameNormENN (∏ index, factors index).val)
      ≤ tameEnvelopeENN parameters grade
          (tupleConvolutionENN (smaller + 1)
            (fun index => tameNormENN (factors index).val)) :=
        tameEnvelopeENN_mono_family grade (tameProd_norm_dominated (smaller + 1) factors)
    _ ≤ ((smaller + 1 : ℕ) : ℝ≥0∞) ^ grade *
          ∑ index, tameEnvelopeENN parameters grade (tameNormENN (factors index).val) *
            ∏ other ∈ Finset.univ.erase index,
              tameEnvelopeENN parameters 0 (tameNormENN (factors other).val) :=
        tupleConvolutionENN_envelope_le parameters grade _
    _ = _ := by
        rw [ENNReal.ofReal_mul (pow_nonneg (Nat.cast_nonneg _) grade),
          ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
          ENNReal.ofReal_sum_of_nonneg (fun index _ => mul_nonneg
            (coefficientEnvelope_nonneg _ _)
            (Finset.prod_nonneg (fun _ _ => coefficientEnvelope_nonneg _ _)))]
        congr 1
        apply Finset.sum_congr rfl
        intro index _
        rw [ENNReal.ofReal_mul (coefficientEnvelope_nonneg _ _),
          ENNReal.ofReal_prod_of_nonneg (fun _ _ => coefficientEnvelope_nonneg _ _),
          tameEnvelopeENN_normENN_eq (factors index).property grade]
        congr 1
        apply Finset.prod_congr rfl
        intro other _
        rw [tameEnvelopeENN_normENN_eq (factors other).property 0]
        rfl

/-- The sharp grade-zero submultiplicativity for nonempty ring products. -/
theorem tameProd_envelope_zero_le {smaller : ℕ}
    (factors : Fin (smaller + 1) → TameCoefficient parameters) :
    coefficientEnvelope 0 (∏ index, factors index) ≤
      ∏ index, coefficientEnvelope 0 (factors index) := by
  have rightNonneg : 0 ≤ ∏ index, coefficientEnvelope 0 (factors index) :=
    Finset.prod_nonneg (fun _ _ => coefficientEnvelope_nonneg _ _)
  rw [← ENNReal.ofReal_le_ofReal_iff rightNonneg, coefficientEnvelope,
    ← tameEnvelopeENN_normENN_eq (∏ index, factors index).property 0]
  calc tameEnvelopeENN parameters 0 (tameNormENN (∏ index, factors index).val)
      ≤ tameEnvelopeENN parameters 0
          (tupleConvolutionENN (smaller + 1)
            (fun index => tameNormENN (factors index).val)) :=
        tameEnvelopeENN_mono_family 0 (tameProd_norm_dominated (smaller + 1) factors)
    _ ≤ ∏ index, tameEnvelopeENN parameters 0 (tameNormENN (factors index).val) :=
        tupleConvolutionENN_envelope_zero_le parameters _
    _ = _ := by
        rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => coefficientEnvelope_nonneg _ _)]
        apply Finset.prod_congr rfl
        intro index _
        rw [tameEnvelopeENN_normENN_eq (factors index).property 0]
        rfl

/-! ### Specialization to binary products and ring powers -/

theorem tameMul_envelope_le (grade : ℕ) (c d : TameCoefficient parameters) :
    coefficientEnvelope grade (c * d) ≤ (2 : ℝ) ^ grade *
      (coefficientEnvelope grade c * coefficientEnvelope 0 d +
        coefficientEnvelope 0 c * coefficientEnvelope grade d) := by
  have eraseZero : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  have eraseOne : (Finset.univ.erase (1 : Fin 2)) = {0} := by decide
  have master := tameProd_envelope_le (parameters := parameters) grade (smaller := 1) ![c, d]
  rw [Fin.prod_univ_two, Fin.sum_univ_two, eraseZero, eraseOne, Finset.prod_singleton,
    Finset.prod_singleton] at master
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at master
  apply master.trans (le_of_eq ?_)
  push_cast
  ring

theorem tameMul_envelope_zero_le (c d : TameCoefficient parameters) :
    coefficientEnvelope 0 (c * d) ≤ coefficientEnvelope 0 c * coefficientEnvelope 0 d := by
  have master := tameProd_envelope_zero_le (parameters := parameters) (smaller := 1) ![c, d]
  rw [Fin.prod_univ_two, Fin.prod_univ_two] at master
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using master

theorem tamePow_eq_prod (c : TameCoefficient parameters) (exponent : ℕ) :
    c ^ exponent = ∏ _index : Fin exponent, c := by
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The graded envelope of a positive ring power: the exact
`p^{s+1} L^{p-1} H` majorant of the root series. -/
theorem tamePow_envelope_le (grade : ℕ) (smaller : ℕ) (c : TameCoefficient parameters) :
    coefficientEnvelope grade (c ^ (smaller + 1)) ≤
      ((smaller + 1 : ℕ) : ℝ) ^ (grade + 1) *
        coefficientEnvelope 0 c ^ smaller * coefficientEnvelope grade c := by
  have master := tameProd_envelope_le (parameters := parameters) grade (smaller := smaller)
    (fun _ => c)
  have summandValue : ∀ index : Fin (smaller + 1), coefficientEnvelope grade c *
      ∏ _other ∈ Finset.univ.erase index, coefficientEnvelope 0 c =
      coefficientEnvelope grade c * coefficientEnvelope 0 c ^ smaller := by
    intro index
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ index),
      Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
  have sumValue : (∑ index : Fin (smaller + 1), coefficientEnvelope grade c *
      ∏ _other ∈ Finset.univ.erase index, coefficientEnvelope 0 c) =
      ((smaller + 1 : ℕ) : ℝ) *
        (coefficientEnvelope grade c * coefficientEnvelope 0 c ^ smaller) := by
    calc (∑ index : Fin (smaller + 1), coefficientEnvelope grade c *
          ∏ _other ∈ Finset.univ.erase index, coefficientEnvelope 0 c)
        = ∑ _index : Fin (smaller + 1),
            coefficientEnvelope grade c * coefficientEnvelope 0 c ^ smaller :=
          Finset.sum_congr rfl (fun index _ => summandValue index)
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [tamePow_eq_prod]
  apply master.trans (le_of_eq ?_)
  rw [sumValue]
  ring

/-- Sharp zero-grade power bound. -/
theorem tamePow_envelope_zero_le (smaller : ℕ) (c : TameCoefficient parameters) :
    coefficientEnvelope 0 (c ^ (smaller + 1)) ≤ coefficientEnvelope 0 c ^ (smaller + 1) := by
  have master := tameProd_envelope_zero_le (parameters := parameters) (smaller := smaller)
    (fun _ => c)
  rw [tamePow_eq_prod]
  apply master.trans_eq
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Grad.NonlinearQuotientBounds
