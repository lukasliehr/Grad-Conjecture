import TameTangent

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! The M17/Q12 Cauchy–Schwarz bridge from the planar `ℓ¹` envelope to the
tangential M16 norm with the literal constant `√2^s C_ax`, and the planar
component families in the scalar coefficient core. -/

variable {parameters : PhaseParameters}

/-- Cauchy–Schwarz for infinite nonnegative sums. -/
theorem tsum_mul_le_sqrt_mul_sqrt (a b : ℤ → ℝ)
    (aNonneg : ∀ cell, 0 ≤ a cell) (bNonneg : ∀ cell, 0 ≤ b cell)
    (aSquare : Summable (fun cell => a cell ^ 2))
    (bSquare : Summable (fun cell => b cell ^ 2)) :
    Summable (fun cell => a cell * b cell) ∧
      (∑' cell, a cell * b cell) ≤
        Real.sqrt (∑' cell, a cell ^ 2) * Real.sqrt (∑' cell, b cell ^ 2) := by
  have product_summable : Summable (fun cell => a cell * b cell) := by
    apply Summable.of_nonneg_of_le
      (fun cell => mul_nonneg (aNonneg cell) (bNonneg cell)) (fun cell => ?_)
      ((aSquare.add bSquare).mul_left (1 / 2))
    have amgm := two_mul_le_add_sq (a cell) (b cell)
    linarith
  refine ⟨product_summable, ?_⟩
  apply product_summable.tsum_le_of_sum_le
  intro finite
  have finite_cs := Finset.sum_mul_sq_le_sq_mul_sq finite a b
  have finite_nonneg : 0 ≤ ∑ cell ∈ finite, a cell * b cell :=
    Finset.sum_nonneg (fun cell _ => mul_nonneg (aNonneg cell) (bNonneg cell))
  have a_partial_le : (∑ cell ∈ finite, a cell ^ 2) ≤ ∑' cell, a cell ^ 2 :=
    aSquare.sum_le_tsum finite (fun cell _ => sq_nonneg _)
  have b_partial_le : (∑ cell ∈ finite, b cell ^ 2) ≤ ∑' cell, b cell ^ 2 :=
    bSquare.sum_le_tsum finite (fun cell _ => sq_nonneg _)
  have a_partial_nonneg : 0 ≤ ∑ cell ∈ finite, a cell ^ 2 :=
    Finset.sum_nonneg (fun cell _ => sq_nonneg _)
  have b_partial_nonneg : 0 ≤ ∑ cell ∈ finite, b cell ^ 2 :=
    Finset.sum_nonneg (fun cell _ => sq_nonneg _)
  calc ∑ cell ∈ finite, a cell * b cell
      = Real.sqrt ((∑ cell ∈ finite, a cell * b cell) ^ 2) :=
        (Real.sqrt_sq finite_nonneg).symm
    _ ≤ Real.sqrt ((∑ cell ∈ finite, a cell ^ 2) * ∑ cell ∈ finite, b cell ^ 2) :=
        Real.sqrt_le_sqrt finite_cs
    _ = Real.sqrt (∑ cell ∈ finite, a cell ^ 2) *
        Real.sqrt (∑ cell ∈ finite, b cell ^ 2) := Real.sqrt_mul a_partial_nonneg _
    _ ≤ Real.sqrt (∑' cell, a cell ^ 2) * Real.sqrt (∑' cell, b cell ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt a_partial_le) (Real.sqrt_le_sqrt b_partial_le)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- One planar `ℓ¹` envelope summand. -/
def tangentPlanarTerm (parameters : PhaseParameters) (grade : ℕ)
    (family : ℤ → ComplexEuclidean 2) (cell : ℤ) : ℝ :=
  tameWeight parameters grade cell * ‖family cell‖

theorem tangentPlanarTerm_nonneg (grade : ℕ) (family : ℤ → ComplexEuclidean 2)
    (cell : ℤ) : 0 ≤ tangentPlanarTerm parameters grade family cell :=
  mul_nonneg (tameWeight_pos parameters grade cell).le (norm_nonneg _)

/-- The square root of one M16 summand. -/
theorem sqrt_tangentNormTerm (grade : ℕ) (family : ℤ → ComplexEuclidean 2) (cell : ℤ) :
    Real.sqrt (tangentNormTerm parameters grade family cell) =
      Real.exp (parameters.sigma0 * cellFrequency cell) *
        cellFrequency cell ^ grade * ‖family cell‖ := by
  have freq_pos : 0 < cellFrequency cell := Grad.CellWeights.cellWeight_pos cell
  have square_form : tangentNormTerm parameters grade family cell =
      (Real.exp (parameters.sigma0 * cellFrequency cell) *
        cellFrequency cell ^ grade * ‖family cell‖) ^ 2 := by
    rw [tangentNormTerm]
    rw [mul_pow, mul_pow, ← pow_mul]
    ring
  rw [square_form]
  apply Real.sqrt_sq
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg freq_pos.le _))
    (norm_nonneg _)

/-- The pointwise M17 splitting of the planar summand. -/
theorem tangentPlanarTerm_le (grade : ℕ) (family : ℤ → ComplexEuclidean 2) (cell : ℤ) :
    tangentPlanarTerm parameters grade family cell ≤
      Real.sqrt 2 ^ grade * ((cellFrequency cell)⁻¹ *
        Real.sqrt (tangentNormTerm parameters (grade + 1) family cell)) := by
  have freq_pos : 0 < cellFrequency cell := Grad.CellWeights.cellWeight_pos cell
  rw [sqrt_tangentNormTerm]
  have polynomial_le : cellPolynomialWeight cell ^ grade ≤
      Real.sqrt 2 ^ grade * cellFrequency cell ^ grade := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (cellPolynomialWeight_pos cell).le
    have square_le : cellPolynomialWeight cell ^ 2 ≤ 2 * cellFrequency cell ^ 2 := by
      rw [cellPolynomialWeight, cellFrequency, Grad.CellBinomial.cellWeight_sq]
      have abs_sq : |(cell : ℝ)| ^ 2 = (cell : ℝ) ^ 2 := sq_abs _
      nlinarith [abs_nonneg ((cell : ℝ)), sq_nonneg (1 - |(cell : ℝ)|)]
    have sqrt_two_freq : Real.sqrt 2 * cellFrequency cell =
        Real.sqrt (2 * cellFrequency cell ^ 2) := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_sq freq_pos.le]
    rw [sqrt_two_freq]
    calc cellPolynomialWeight cell
        = Real.sqrt (cellPolynomialWeight cell ^ 2) :=
          (Real.sqrt_sq (cellPolynomialWeight_pos cell).le).symm
      _ ≤ _ := Real.sqrt_le_sqrt square_le
  have frequency_collapse : (cellFrequency cell)⁻¹ *
      (Real.exp (parameters.sigma0 * cellFrequency cell) *
        cellFrequency cell ^ (grade + 1) * ‖family cell‖) =
      Real.exp (parameters.sigma0 * cellFrequency cell) *
        cellFrequency cell ^ grade * ‖family cell‖ := by
    rw [pow_succ]
    field_simp
  rw [frequency_collapse]
  calc tangentPlanarTerm parameters grade family cell
      = Real.exp (parameters.sigma0 * cellFrequency cell) *
          cellPolynomialWeight cell ^ grade * ‖family cell‖ := by
        rw [tangentPlanarTerm, tameWeight]
    _ ≤ Real.exp (parameters.sigma0 * cellFrequency cell) *
          (Real.sqrt 2 ^ grade * cellFrequency cell ^ grade) * ‖family cell‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left polynomial_le (Real.exp_pos _).le
    _ = _ := by ring

/-- The planar `ℓ¹` envelope of a tangential family at one grade. -/
def tangentPlanarEnvelope (grade : ℕ) (family : TangentCoefficient parameters) : ℝ :=
  ∑' cell, tangentPlanarTerm parameters grade family.val cell

theorem sqrt_term_square (grade : ℕ) (family : TangentCoefficient parameters) (cell : ℤ) :
    Real.sqrt (tangentNormTerm parameters grade family.val cell) ^ 2 =
      tangentNormTerm parameters grade family.val cell :=
  Real.sq_sqrt (tangentNormTerm_nonneg grade family.val cell)

theorem inverse_frequency_square (cell : ℤ) :
    ((cellFrequency cell)⁻¹) ^ 2 = inverseSquareFrequency cell := by
  rw [inverseSquareFrequency, inv_pow]

/-- The planar Cauchy–Schwarz data of a tangential family. -/
theorem tangentPlanar_summable_and_le (grade : ℕ) (family : TangentCoefficient parameters) :
    Summable (tangentPlanarTerm parameters grade family.val) ∧
      tangentPlanarEnvelope grade family ≤
        Real.sqrt 2 ^ grade * (axisConstant * tangentNorm (grade + 1) family) := by
  have freq_inv_nonneg : ∀ cell : ℤ, 0 ≤ (cellFrequency cell)⁻¹ := by
    intro cell
    have := Grad.CellWeights.cellWeight_pos cell
    positivity
  have sqrt_nonneg : ∀ cell : ℤ, 0 ≤
      Real.sqrt (tangentNormTerm parameters (grade + 1) family.val cell) :=
    fun cell => Real.sqrt_nonneg _
  have a_square : Summable (fun cell => ((cellFrequency cell)⁻¹) ^ 2) := by
    apply inverseSquareFrequency_summable.congr
    intro cell
    rw [inverse_frequency_square]
  have b_square : Summable (fun cell =>
      Real.sqrt (tangentNormTerm parameters (grade + 1) family.val cell) ^ 2) := by
    apply (family.property (grade + 1)).congr
    intro cell
    rw [sqrt_term_square]
  obtain ⟨product_summable, product_le⟩ := tsum_mul_le_sqrt_mul_sqrt _ _
    freq_inv_nonneg sqrt_nonneg a_square b_square
  have planar_summable : Summable (tangentPlanarTerm parameters grade family.val) := by
    apply Summable.of_nonneg_of_le (tangentPlanarTerm_nonneg grade family.val)
      (tangentPlanarTerm_le grade family.val)
      (product_summable.mul_left (Real.sqrt 2 ^ grade))
  refine ⟨planar_summable, ?_⟩
  have a_square_tsum_le : (∑' cell, ((cellFrequency cell)⁻¹) ^ 2) ≤ 1 + Real.pi := by
    calc (∑' cell, ((cellFrequency cell)⁻¹) ^ 2)
        = ∑' cell, inverseSquareFrequency cell :=
          tsum_congr (fun cell => inverse_frequency_square cell)
      _ ≤ _ := inverseSquareFrequency_tsum_le
  have b_square_tsum : (∑' cell,
      Real.sqrt (tangentNormTerm parameters (grade + 1) family.val cell) ^ 2) =
      ∑' cell, tangentNormTerm parameters (grade + 1) family.val cell :=
    tsum_congr (fun cell => sqrt_term_square (grade + 1) family cell)
  calc tangentPlanarEnvelope grade family
      ≤ ∑' cell, Real.sqrt 2 ^ grade * ((cellFrequency cell)⁻¹ *
          Real.sqrt (tangentNormTerm parameters (grade + 1) family.val cell)) :=
        planar_summable.tsum_le_tsum (tangentPlanarTerm_le grade family.val)
          (product_summable.mul_left _)
    _ = Real.sqrt 2 ^ grade * ∑' cell, (cellFrequency cell)⁻¹ *
          Real.sqrt (tangentNormTerm parameters (grade + 1) family.val cell) :=
        tsum_mul_left
    _ ≤ Real.sqrt 2 ^ grade * (Real.sqrt (∑' cell, ((cellFrequency cell)⁻¹) ^ 2) *
          Real.sqrt (∑' cell,
            Real.sqrt (tangentNormTerm parameters (grade + 1) family.val cell) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left product_le (pow_nonneg (Real.sqrt_nonneg 2) grade)
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Real.sqrt_nonneg 2) grade)
        rw [b_square_tsum]
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        rw [axisConstant]
        exact Real.sqrt_le_sqrt a_square_tsum_le

theorem tangentPlanar_summable (grade : ℕ) (family : TangentCoefficient parameters) :
    Summable (tangentPlanarTerm parameters grade family.val) :=
  (tangentPlanar_summable_and_le grade family).1

/-- The literal M17/Q12 bridge with the exact constant `√2^s C_ax`. -/
theorem tangentPlanarEnvelope_le (grade : ℕ) (family : TangentCoefficient parameters) :
    tangentPlanarEnvelope grade family ≤
      Real.sqrt 2 ^ grade * (axisConstant * tangentNorm (grade + 1) family) :=
  (tangentPlanar_summable_and_le grade family).2

theorem tangentPlanarEnvelope_nonneg (grade : ℕ) (family : TangentCoefficient parameters) :
    0 ≤ tangentPlanarEnvelope grade family :=
  tsum_nonneg (fun cell => tangentPlanarTerm_nonneg grade family.val cell)

/-! ### Planar components in the scalar coefficient core -/

theorem euclidean_component_norm_le (vector : ComplexEuclidean 2) (index : Fin 2) :
    ‖vector index‖ ≤ ‖vector‖ := by
  rw [EuclideanSpace.norm_eq]
  have square_le : ‖vector index‖ ^ 2 ≤ ∑ other, ‖vector other‖ ^ 2 :=
    Finset.single_le_sum (f := fun other => ‖vector other‖ ^ 2)
      (fun other _ => sq_nonneg _) (Finset.mem_univ index)
  calc ‖vector index‖ = Real.sqrt (‖vector index‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt square_le

theorem tangentComponent_summable (family : TangentCoefficient parameters) (index : Fin 2) :
    TameSummableFamily parameters (fun cell => family.val cell index) := by
  intro grade
  apply Summable.of_nonneg_of_le (fun cell => tameEnvelopeTerm_nonneg parameters grade _ cell)
    (fun cell => ?_) (tangentPlanar_summable grade family)
  rw [tameEnvelopeTerm, tangentPlanarTerm]
  exact mul_le_mul_of_nonneg_left (euclidean_component_norm_le (family.val cell) index)
    (tameWeight_pos parameters grade cell).le

/-- One planar component as a scalar coefficient-core element. -/
def tangentComponent (family : TangentCoefficient parameters) (index : Fin 2) :
    TameCoefficient parameters :=
  ⟨fun cell => family.val cell index, tangentComponent_summable family index⟩

theorem tangentComponent_val (family : TangentCoefficient parameters) (index : Fin 2)
    (cell : ℤ) : (tangentComponent family index).val cell = family.val cell index := rfl

theorem tangentComponent_envelope_le (grade : ℕ) (family : TangentCoefficient parameters)
    (index : Fin 2) :
    coefficientEnvelope grade (tangentComponent family index) ≤
      tangentPlanarEnvelope grade family := by
  apply ((tangentComponent family index).property grade).tsum_le_tsum
    (fun cell => ?_) (tangentPlanar_summable grade family)
  rw [tameEnvelopeTerm, tangentComponent_val, tangentPlanarTerm]
  exact mul_le_mul_of_nonneg_left (euclidean_component_norm_le (family.val cell) index)
    (tameWeight_pos parameters grade cell).le

theorem tangentComponent_add (first second : TangentCoefficient parameters) (index : Fin 2) :
    tangentComponent (first + second) index =
      tangentComponent first index + tangentComponent second index := rfl

theorem tangentComponent_smul (scalar : ℂ) (family : TangentCoefficient parameters)
    (index : Fin 2) :
    tangentComponent (scalar • family) index = scalar • tangentComponent family index := rfl

end Grad.NonlinearQuotientBounds
