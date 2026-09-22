import MultiplierJet

noncomputable section

open scoped BigOperators

namespace Grad.Constraints.Multipliers

open Grad.ClosedJets Grad.CartesianState Grad.AnalyticWeights.Higher

def wordShiftConstant (rank : ℕ) (gamma : ℝ) : ℝ :=
  ∑ selected : Finset (Fin rank), ratioDerivativeConstant selected.card gamma

def gradeShiftConstant (grade : ℕ) (gamma : ℝ) : ℝ :=
  ∑ rank ∈ Finset.range (grade + 1), wordShiftConstant rank gamma

theorem wordShiftConstant_nonnegative (rank : ℕ) (gamma : ℝ) (gammaNonnegative : 0 ≤ gamma) :
    0 ≤ wordShiftConstant rank gamma :=
  Finset.sum_nonneg (fun _ _ => ratioDerivativeConstant_nonnegative _ _ gammaNonnegative)

theorem gradeShiftConstant_nonnegative (grade : ℕ) (gamma : ℝ) (gammaNonnegative : 0 ≤ gamma) :
    0 ≤ gradeShiftConstant grade gamma :=
  Finset.sum_nonneg (fun _ _ => wordShiftConstant_nonnegative _ _ gammaNonnegative)

theorem wordShiftConstant_le_gradeShiftConstant {rank grade : ℕ} (rankBound : rank ≤ grade)
    (gamma : ℝ) (gammaNonnegative : 0 ≤ gamma) :
    wordShiftConstant rank gamma ≤ gradeShiftConstant grade gamma := by
  apply Finset.single_le_sum (fun index _ => wordShiftConstant_nonnegative index gamma gammaNonnegative)
  exact Finset.mem_range.mpr (by omega)

theorem allocated_frequency_bound (input shift : ℤ) (grade first second : ℕ)
    (orderBound : first + second ≤ grade) :
    cellFrequency (input + shift) ^ (grade - (first + second)) *
        cellPolynomialWeight shift ^ first * cellFrequency input ^ first ≤
      cellPolynomialWeight shift ^ grade * cellFrequency input ^ (grade - second) := by
  have polynomialNonnegative : 0 ≤ cellPolynomialWeight shift :=
    (zero_lt_one.trans_le (cellPolynomialWeight_one_le shift)).le
  have inputNonnegative := (cellFrequency_pos input).le
  calc
    _ ≤ (cellPolynomialWeight shift * cellFrequency input) ^ (grade - (first + second)) *
        cellPolynomialWeight shift ^ first * cellFrequency input ^ first := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (cellFrequency_pos _).le (shifted_frequency_le input shift) _)
          (pow_nonneg polynomialNonnegative _)) (pow_nonneg inputNonnegative _)
    _ = cellPolynomialWeight shift ^ (grade - second) * cellFrequency input ^ (grade - second) := by
      have exponents : grade - (first + second) + first = grade - second := by omega
      rw [mul_pow]
      calc
        _ = (cellPolynomialWeight shift ^ (grade - (first + second)) * cellPolynomialWeight shift ^ first) *
            (cellFrequency input ^ (grade - (first + second)) * cellFrequency input ^ first) := by ring
        _ = _ := by rw [← pow_add, ← pow_add, exponents]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (cellPolynomialWeight_one_le shift) (Nat.sub_le grade second))
      (pow_nonneg inputNonnegative _)

theorem weighted_shiftedTerm_bound {dimension rank grade : ℕ} (parameters : PhaseParameters)
    (input shift : ℤ) (field : ClosedJet dimension) (word : CartesianWord rank)
    (rankBound : rank ≤ grade) (selected : Finset (Fin rank)) :
    cellFrequency (input + shift) ^ (grade - rank) *
        ‖closedContinuousToDiskL2 (shiftedDerivativeTerm parameters input shift field word selected)‖ ≤
      ratioDerivativeConstant selected.card parameters.gamma *
        Real.exp (parameters.sigma0 * cellFrequency shift) * cellPolynomialWeight shift ^ grade *
        ‖cellGradeRowLinear (grade := grade) parameters input field‖ := by
  have splitOrder : selected.card + selectedᶜ.card = rank := by
    simp
  have complementBound : selectedᶜ.card ≤ grade := by omega
  have constantNonnegative := ratioDerivativeConstant_nonnegative selected.card parameters.gamma parameters.gamma_pos.le
  have expNonnegative := (Real.exp_pos (parameters.sigma0 * cellFrequency shift)).le
  have polynomialNonnegative : 0 ≤ cellPolynomialWeight shift :=
    (zero_lt_one.trans_le (cellPolynomialWeight_one_le shift)).le
  let derivativeNorm := ‖closedContinuousToDiskL2 (closedDerivative
    (phaseWeightedJet parameters input field) selectedᶜ.card (subword word selectedᶜ))‖
  have derivativeNonnegative : 0 ≤ derivativeNorm := norm_nonneg _
  calc
    _ ≤ cellFrequency (input + shift) ^ (grade - rank) *
        ((ratioDerivativeConstant selected.card parameters.gamma *
          Real.exp (parameters.sigma0 * cellFrequency shift) * cellPolynomialWeight shift ^ selected.card *
          cellFrequency input ^ selected.card) * derivativeNorm) :=
      mul_le_mul_of_nonneg_left (shiftedDerivativeTerm_L2_bound parameters input shift field word selected)
        (pow_nonneg (cellFrequency_pos _).le _)
    _ = (ratioDerivativeConstant selected.card parameters.gamma *
          Real.exp (parameters.sigma0 * cellFrequency shift)) *
        (cellFrequency (input + shift) ^ (grade - (selected.card + selectedᶜ.card)) *
          cellPolynomialWeight shift ^ selected.card * cellFrequency input ^ selected.card) * derivativeNorm := by
      rw [splitOrder]; ring
    _ ≤ (ratioDerivativeConstant selected.card parameters.gamma *
          Real.exp (parameters.sigma0 * cellFrequency shift)) *
        (cellPolynomialWeight shift ^ grade * cellFrequency input ^ (grade - selectedᶜ.card)) * derivativeNorm := by
      apply mul_le_mul_of_nonneg_right _ derivativeNonnegative
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg constantNonnegative expNonnegative)
      exact allocated_frequency_bound input shift grade selected.card selectedᶜ.card (by omega)
    _ = (ratioDerivativeConstant selected.card parameters.gamma *
          Real.exp (parameters.sigma0 * cellFrequency shift) * cellPolynomialWeight shift ^ grade) *
        (cellFrequency input ^ (grade - selectedᶜ.card) * derivativeNorm) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (weighted_word_norm_le_row parameters input field complementBound (subword word selectedᶜ))
      (mul_nonneg (mul_nonneg constantNonnegative expNonnegative) (pow_nonneg polynomialNonnegative _))

theorem shifted_weighted_word_norm_le {dimension rank grade : ℕ} (parameters : PhaseParameters)
    (input shift : ℤ) (field : ClosedJet dimension) (word : CartesianWord rank)
    (rankBound : rank ≤ grade) :
    cellFrequency (input + shift) ^ (grade - rank) *
      ‖closedContinuousToDiskL2 (closedDerivative (phaseWeightedJet parameters (input + shift) field)
        rank word)‖ ≤
      gradeShiftConstant grade parameters.gamma *
        Real.exp (parameters.sigma0 * cellFrequency shift) * cellPolynomialWeight shift ^ grade *
        ‖cellGradeRowLinear (grade := grade) parameters input field‖ := by
  rw [shifted_weighted_derivative]
  change cellFrequency (input + shift) ^ (grade - rank) *
    ‖closedValueL2Linear dimension
      (∑ selected : Finset (Fin rank), shiftedDerivativeTerm parameters input shift field word selected)‖ ≤ _
  rw [map_sum]
  calc
    _ ≤ cellFrequency (input + shift) ^ (grade - rank) *
        ∑ selected : Finset (Fin rank),
          ‖closedContinuousToDiskL2 (shiftedDerivativeTerm parameters input shift field word selected)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg (cellFrequency_pos _).le _)
    _ = ∑ selected : Finset (Fin rank), cellFrequency (input + shift) ^ (grade - rank) *
          ‖closedContinuousToDiskL2 (shiftedDerivativeTerm parameters input shift field word selected)‖ :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ selected : Finset (Fin rank), ratioDerivativeConstant selected.card parameters.gamma *
        Real.exp (parameters.sigma0 * cellFrequency shift) * cellPolynomialWeight shift ^ grade *
        ‖cellGradeRowLinear (grade := grade) parameters input field‖ :=
      Finset.sum_le_sum (fun selected _ => weighted_shiftedTerm_bound parameters input shift field word rankBound selected)
    _ = wordShiftConstant rank parameters.gamma *
        Real.exp (parameters.sigma0 * cellFrequency shift) * cellPolynomialWeight shift ^ grade *
        ‖cellGradeRowLinear (grade := grade) parameters input field‖ := by
      simp only [wordShiftConstant, Finset.sum_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg
        (zero_lt_one.trans_le (cellPolynomialWeight_one_le shift)).le _)
      exact mul_le_mul_of_nonneg_right
        (wordShiftConstant_le_gradeShiftConstant rankBound parameters.gamma parameters.gamma_pos.le)
        (Real.exp_pos _).le

def multiplierConstant (grade : ℕ) (gamma : ℝ) : ℝ :=
  Real.sqrt (Fintype.card (GradeMultiIndex grade)) * gradeShiftConstant grade gamma

theorem multiplierConstant_nonnegative (grade : ℕ) (gamma : ℝ) (gammaNonnegative : 0 ≤ gamma) :
    0 ≤ multiplierConstant grade gamma :=
  mul_nonneg (Real.sqrt_nonneg _) (gradeShiftConstant_nonnegative grade gamma gammaNonnegative)

theorem shifted_grade_row_bound {dimension grade : ℕ} (parameters : PhaseParameters)
    (input shift : ℤ) (field : ClosedJet dimension) :
    ‖cellGradeRowLinear (grade := grade) parameters (input + shift) field‖ ≤
      multiplierConstant grade parameters.gamma *
        Real.exp (parameters.sigma0 * cellFrequency shift) * cellPolynomialWeight shift ^ grade *
        ‖cellGradeRowLinear (grade := grade) parameters input field‖ := by
  let row := cellGradeRowLinear (grade := grade) parameters (input + shift) field
  let bound := gradeShiftConstant grade parameters.gamma *
    Real.exp (parameters.sigma0 * cellFrequency shift) * cellPolynomialWeight shift ^ grade *
    ‖cellGradeRowLinear (grade := grade) parameters input field‖
  have boundNonnegative : 0 ≤ bound := mul_nonneg
    (mul_nonneg (mul_nonneg (gradeShiftConstant_nonnegative _ _ parameters.gamma_pos.le)
      (Real.exp_pos _).le) (pow_nonneg (zero_lt_one.trans_le (cellPolynomialWeight_one_le shift)).le _))
    (norm_nonneg _)
  have coordinateBound (index : GradeMultiIndex grade) : ‖row index‖ ≤ bound := by
    dsimp [row]
    rw [cellGradeRowLinear_apply, norm_smul, Complex.norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (cellFrequency_pos _).le]
    exact shifted_weighted_word_norm_le parameters input shift field
      (cartesianMultiIndexWord index.toCartesian) index.property
  have squareBound : ‖row‖ ^ 2 ≤ (Fintype.card (GradeMultiIndex grade) : ℝ) * bound ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _index : GradeMultiIndex grade, bound ^ 2 :=
        Finset.sum_le_sum (fun index _ => pow_le_pow_left₀ (norm_nonneg _) (coordinateBound index) 2)
      _ = _ := by simp
  have rootSquare := Real.sq_sqrt
    (show (0 : ℝ) ≤ Fintype.card (GradeMultiIndex grade) by positivity)
  have rootNonnegative := Real.sqrt_nonneg (Fintype.card (GradeMultiIndex grade) : ℝ)
  have productNonnegative := mul_nonneg rootNonnegative boundNonnegative
  have result : ‖row‖ ≤ Real.sqrt (Fintype.card (GradeMultiIndex grade) : ℝ) * bound := by
    nlinarith [sq_nonneg (‖row‖ - Real.sqrt (Fintype.card (GradeMultiIndex grade) : ℝ) * bound)]
  dsimp [row, bound] at result
  simpa only [multiplierConstant, mul_assoc] using result

theorem mapped_shifted_grade_row_bound {sourceDimension targetDimension grade : ℕ}
    (parameters : PhaseParameters) (input shift : ℤ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : ClosedJet sourceDimension) :
    ‖cellGradeRowLinear (grade := grade) parameters (input + shift) (valueMapJet mapping field)‖ ≤
      multiplierConstant grade parameters.gamma *
        Real.exp (parameters.sigma0 * cellFrequency shift) * cellPolynomialWeight shift ^ grade *
        ‖mapping‖ * ‖cellGradeRowLinear (grade := grade) parameters input field‖ := by
  apply (valueMap_grade_row_bound mapping parameters (input + shift) field).trans
  calc
    _ ≤ ‖mapping‖ * (multiplierConstant grade parameters.gamma *
        Real.exp (parameters.sigma0 * cellFrequency shift) * cellPolynomialWeight shift ^ grade *
        ‖cellGradeRowLinear (grade := grade) parameters input field‖) :=
      mul_le_mul_of_nonneg_left (shifted_grade_row_bound parameters input shift field) (norm_nonneg _)
    _ = _ := by ring

end Grad.Constraints.Multipliers
