import TameEnvDerivative

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! Algebraic interchange laws for majorized series in the coefficient core:
scalar tower instances for the convolution ring, multiplication of a series
by a fixed element, and the index-shift decomposition used by the root-series
Taylor remainders. -/

variable {parameters : PhaseParameters}

instance : IsScalarTower ℂ (TameCoefficient parameters) (TameCoefficient parameters) :=
  ⟨fun scalar c d => by
    change ((scalar • c) * d) = scalar • (c * d)
    exact tameSmul_mul scalar c d⟩

instance : SMulCommClass ℂ (TameCoefficient parameters) (TameCoefficient parameters) :=
  ⟨fun scalar c d => by
    change scalar • (c * d) = c * (scalar • d)
    exact (tameMul_smul scalar c d).symm⟩

/-- Multiplying a majorized series by a fixed element, term by term. -/
theorem SeriesMajorant.mul_fixed {Index : Type}
    {terms : Index → TameCoefficient parameters} {majorant : ℕ → Index → ℝ}
    (major : SeriesMajorant terms majorant) (fixed : TameCoefficient parameters) :
    SeriesMajorant (fun index => terms index * fixed)
      (fun grade index => (2 : ℝ) ^ grade *
        (majorant grade index * coefficientEnvelope 0 fixed +
          majorant 0 index * coefficientEnvelope grade fixed)) := by
  intro grade
  constructor
  · intro index
    calc coefficientEnvelope grade (terms index * fixed)
        ≤ (2 : ℝ) ^ grade *
            (coefficientEnvelope grade (terms index) * coefficientEnvelope 0 fixed +
              coefficientEnvelope 0 (terms index) * coefficientEnvelope grade fixed) :=
          tameMul_envelope_le grade _ _
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) grade)
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right ((major grade).1 index)
              (coefficientEnvelope_nonneg _ _)
          · exact mul_le_mul_of_nonneg_right ((major 0).1 index)
              (coefficientEnvelope_nonneg _ _)
  · apply Summable.mul_left
    exact (((major grade).2.mul_right _).add ((major 0).2.mul_right _))

theorem tameSeries_mul_fixed {Index : Type}
    (terms : Index → TameCoefficient parameters) {majorant : ℕ → Index → ℝ}
    (major : SeriesMajorant terms majorant) (fixed : TameCoefficient parameters) :
    tameSeries terms major * fixed =
      tameSeries (fun index => terms index * fixed) (major.mul_fixed fixed) := by
  apply Subtype.ext
  funext cell
  have uncurried : Summable (Function.uncurry (fun (shift : ℤ) (index : Index) =>
      (terms index).val shift * fixed.val (cell - shift))) := by
    apply Summable.of_norm
    have slice_summable (shift : ℤ) : Summable (fun index : Index =>
        ‖(terms index).val shift * fixed.val (cell - shift)‖) := by
      apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun index => ?_)
        ((major.value_norm_summable shift).mul_right ‖fixed.val (cell - shift)‖)
      rw [norm_mul]
    have slice_total_le (shift : ℤ) : (∑' index : Index,
        ‖(terms index).val shift * fixed.val (cell - shift)‖) ≤
        (∑' index, majorant 0 index) * tameEnvelopeTerm parameters 0 fixed.val (cell - shift) := by
      have pointwise (index : Index) : ‖(terms index).val shift * fixed.val (cell - shift)‖ ≤
          majorant 0 index * tameEnvelopeTerm parameters 0 fixed.val (cell - shift) := by
        rw [norm_mul]
        apply mul_le_mul
        · exact (norm_le_tameEnvelope (terms index).property 0 shift).trans ((major 0).1 index)
        · exact norm_le_tameEnvelopeTerm parameters 0 fixed.val (cell - shift)
        · exact norm_nonneg _
        · exact ((coefficientEnvelope_nonneg 0 (terms index)).trans ((major 0).1 index))
      calc (∑' index, ‖(terms index).val shift * fixed.val (cell - shift)‖)
          ≤ ∑' index, majorant 0 index *
              tameEnvelopeTerm parameters 0 fixed.val (cell - shift) :=
            (slice_summable shift).tsum_le_tsum pointwise
              (((major 0).2).mul_right _)
        _ = _ := tsum_mul_right
    apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
    constructor
    · intro shift
      exact slice_summable shift
    · apply Summable.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => norm_nonneg _))
        slice_total_le
      apply Summable.mul_left
      have reindex := (Equiv.subLeft cell).summable_iff
        (f := fun other => tameEnvelopeTerm parameters 0 fixed.val other)
      exact reindex.mpr (fixed.property 0)
  calc (tameSeries terms major * fixed).val cell
      = ∑' shift, (∑' index, (terms index).val shift) * fixed.val (cell - shift) := rfl
    _ = ∑' shift, ∑' index, (terms index).val shift * fixed.val (cell - shift) := by
        apply tsum_congr
        intro shift
        exact tsum_mul_right.symm
    _ = ∑' index, ∑' shift, (terms index).val shift * fixed.val (cell - shift) :=
        uncurried.tsum_comm.symm
    _ = (tameSeries (fun index => terms index * fixed) (major.mul_fixed fixed)).val cell := rfl

/-- Scaling a majorized series term by term. -/
theorem SeriesMajorant.const_smul {Index : Type}
    {terms : Index → TameCoefficient parameters} {majorant : ℕ → Index → ℝ}
    (major : SeriesMajorant terms majorant) (scalar : ℂ) :
    SeriesMajorant (fun index => scalar • terms index)
      (fun grade index => ‖scalar‖ * majorant grade index) := by
  intro grade
  constructor
  · intro index
    rw [coefficientEnvelope_smul]
    exact mul_le_mul_of_nonneg_left ((major grade).1 index) (norm_nonneg _)
  · exact ((major grade).2).mul_left _

theorem tameSeries_const_smul {Index : Type}
    (terms : Index → TameCoefficient parameters) {majorant : ℕ → Index → ℝ}
    (major : SeriesMajorant terms majorant) (scalar : ℂ) :
    scalar • tameSeries terms major =
      tameSeries (fun index => scalar • terms index) (major.const_smul scalar) := by
  apply Subtype.ext
  funext cell
  calc (scalar • tameSeries terms major).val cell
      = scalar * ∑' index, (terms index).val cell := rfl
    _ = ∑' index, scalar * (terms index).val cell := tsum_mul_left.symm
    _ = _ := rfl

/-- Termwise difference of two majorized series over the same index type. -/
theorem SeriesMajorant.sub {Index : Type}
    {firstTerms secondTerms : Index → TameCoefficient parameters}
    {firstMajorant secondMajorant : ℕ → Index → ℝ}
    (first : SeriesMajorant firstTerms firstMajorant)
    (second : SeriesMajorant secondTerms secondMajorant) :
    SeriesMajorant (fun index => firstTerms index - secondTerms index)
      (fun grade index => firstMajorant grade index + secondMajorant grade index) := by
  intro grade
  constructor
  · intro index
    exact (coefficientEnvelope_sub_le grade _ _).trans
      (add_le_add ((first grade).1 index) ((second grade).1 index))
  · exact ((first grade).2).add ((second grade).2)

theorem tameSeries_sub {Index : Type}
    (firstTerms secondTerms : Index → TameCoefficient parameters)
    {firstMajorant secondMajorant : ℕ → Index → ℝ}
    (first : SeriesMajorant firstTerms firstMajorant)
    (second : SeriesMajorant secondTerms secondMajorant) :
    tameSeries firstTerms first - tameSeries secondTerms second =
      tameSeries (fun index => firstTerms index - secondTerms index) (first.sub second) := by
  apply Subtype.ext
  funext cell
  calc (tameSeries firstTerms first - tameSeries secondTerms second).val cell
      = (∑' index, (firstTerms index).val cell) - ∑' index, (secondTerms index).val cell := rfl
    _ = ∑' index, ((firstTerms index).val cell - (secondTerms index).val cell) :=
        ((first.value_summable cell).tsum_sub (second.value_summable cell)).symm
    _ = _ := rfl

/-- Dropping a vanishing zeroth term: shift a natural-indexed series. -/
theorem SeriesMajorant.shift {terms : ℕ → TameCoefficient parameters}
    {majorant : ℕ → ℕ → ℝ} (major : SeriesMajorant terms majorant) :
    SeriesMajorant (fun index => terms (index + 1))
      (fun grade index => majorant grade (index + 1)) := by
  intro grade
  exact ⟨fun index => (major grade).1 (index + 1),
    (summable_nat_add_iff 1).mpr (major grade).2⟩

theorem tameSeries_shift_of_zeroth_zero {terms : ℕ → TameCoefficient parameters}
    {majorant : ℕ → ℕ → ℝ} (major : SeriesMajorant terms majorant)
    (zeroth : terms 0 = 0) :
    tameSeries terms major = tameSeries (fun index => terms (index + 1)) major.shift := by
  apply Subtype.ext
  funext cell
  calc (tameSeries terms major).val cell
      = ∑' index, (terms index).val cell := rfl
    _ = (terms 0).val cell + ∑' index, (terms (index + 1)).val cell :=
        (major.value_summable cell).tsum_eq_zero_add
    _ = ∑' index, (terms (index + 1)).val cell := by
        rw [zeroth, tameZero_val, Pi.zero_apply, zero_add]
    _ = _ := rfl

end Grad.NonlinearQuotientBounds
