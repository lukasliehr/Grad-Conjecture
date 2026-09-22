import AxisTraceMembership

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory

namespace Grad.AxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds

variable {parameters : PhaseParameters}

/-! ### Row-norm plumbing -/

theorem raw_norm_eq_row {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (coefficients : ℤ → ClosedJet dimension) (cell : ℤ) :
    ‖rawCartesianGradeCoordinates parameters grade coefficients cell‖ =
      ‖cellGradeRowLinear (grade := grade) parameters cell (coefficients cell)‖ := by
  have firstSquare := rawCartesianGradeCoordinates_norm_sq parameters grade coefficients cell
  have secondSquare := cellGradeRow_norm_sq (grade := grade) parameters cell
    (coefficients cell)
  have squares : ‖rawCartesianGradeCoordinates parameters grade coefficients cell‖ ^ 2 =
      ‖cellGradeRowLinear (grade := grade) parameters cell (coefficients cell)‖ ^ 2 := by
    rw [firstSquare, secondSquare]
    rfl
  calc ‖rawCartesianGradeCoordinates parameters grade coefficients cell‖ =
      Real.sqrt (‖rawCartesianGradeCoordinates parameters grade coefficients cell‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖cellGradeRowLinear (grade := grade) parameters cell
        (coefficients cell)‖ ^ 2) := by rw [squares]
    _ = ‖cellGradeRowLinear (grade := grade) parameters cell (coefficients cell)‖ :=
        Real.sqrt_sq (norm_nonneg _)

theorem row_norm_memlp {dimension : ℕ} (field : ACore parameters dimension) (grade : ℕ) :
    Memℓp (fun cell => ‖cellGradeRowLinear (grade := grade) parameters cell
      (field.val cell)‖) 2 := by
  have rawMember := (field.property grade).norm
  apply rawMember.mono'
  intro cell
  rw [Real.norm_of_nonneg (norm_nonneg _), raw_norm_eq_row]
  exact (Real.norm_of_nonneg (norm_nonneg _)).ge

theorem row_mono {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) {lower upper : ℕ} (gradeLe : lower ≤ upper) :
    ‖cellGradeRowLinear (grade := lower) parameters cell field‖ ≤
      ‖cellGradeRowLinear (grade := upper) parameters cell field‖ := by
  induction upper with
  | zero =>
    have lowerZero : lower = 0 := Nat.le_zero.mp gradeLe
    rw [lowerZero]
  | succ previous inductionHypothesis =>
    rcases Nat.lt_or_ge lower (previous + 1) with strict | equal
    · have stepBound : ‖cellGradeRowLinear (grade := previous) parameters cell field‖ ≤
          ‖cellGradeRowLinear (grade := previous + 1) parameters cell field‖ := by
        have frequencyStep := cellGradeRow_frequency_bound parameters previous cell field
        have oneLe := cellFrequency_one_le cell
        nlinarith [norm_nonneg (cellGradeRowLinear (grade := previous) parameters cell field)]
      exact (inductionHypothesis (Nat.lt_succ_iff.mp strict)).trans stepBound
    · have lowerEq : lower = previous + 1 := le_antisymm gradeLe equal
      rw [lowerEq]

/-! ### Planar pair norms -/

theorem planarPair_norm_le (first second : ℂ) :
    ‖planarPair first second‖ ≤ ‖first‖ + ‖second‖ := by
  have normSquare : ‖planarPair first second‖ ^ 2 = ‖first‖ ^ 2 + ‖second‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    rw [Fin.sum_univ_two]
    rfl
  have sumSquare : ‖first‖ ^ 2 + ‖second‖ ^ 2 ≤ (‖first‖ + ‖second‖) ^ 2 := by
    nlinarith [norm_nonneg first, norm_nonneg second]
  calc ‖planarPair first second‖ =
      Real.sqrt (‖planarPair first second‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((‖first‖ + ‖second‖) ^ 2) :=
        Real.sqrt_le_sqrt (by rw [normSquare]; exact sumSquare)
    _ = ‖first‖ + ‖second‖ :=
        Real.sqrt_sq (add_nonneg (norm_nonneg _) (norm_nonneg _))

theorem planarJPair_norm (point : ComplexEuclidean 2) :
    ‖planarJPair point‖ = ‖point‖ := by
  have firstSquare : ‖planarJPair point‖ ^ 2 = ‖-(point 1)‖ ^ 2 + ‖point 0‖ ^ 2 := by
    rw [show planarJPair point = planarPair (-(point 1)) (point 0) from rfl,
      PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
    rfl
  have secondSquare : ‖point‖ ^ 2 = ‖point 0‖ ^ 2 + ‖point 1‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  have squares : ‖planarJPair point‖ ^ 2 = ‖point‖ ^ 2 := by
    rw [firstSquare, secondSquare, norm_neg]
    ring
  calc ‖planarJPair point‖ = Real.sqrt (‖planarJPair point‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖point‖ ^ 2) := by rw [squares]
    _ = ‖point‖ := Real.sqrt_sq (norm_nonneg _)

/-! ### The two-row membership criterion -/

theorem mem_axisCore_of_two_rows {firstDimension secondDimension : ℕ}
    (sequence : ℤ → ComplexEuclidean 2) (offset : ℕ) (bound : ℝ)
    (first : ACore parameters firstDimension) (second : ACore parameters secondDimension)
    (dominated : ∀ (grade : ℕ) (cell : ℤ),
      axisWeight parameters grade cell * ‖sequence cell‖ ≤
        bound * (‖cellGradeRowLinear (grade := grade + offset) parameters cell
            (first.val cell)‖ +
          ‖cellGradeRowLinear (grade := grade + offset) parameters cell
            (second.val cell)‖)) :
    sequence ∈ axisCoreSubmodule parameters := by
  intro grade
  have majorantMember : Memℓp (fun cell => bound *
      (‖cellGradeRowLinear (grade := grade + offset) parameters cell (first.val cell)‖ +
        ‖cellGradeRowLinear (grade := grade + offset) parameters cell
          (second.val cell)‖)) 2 :=
    ((row_norm_memlp first (grade + offset)).add
      (row_norm_memlp second (grade + offset))).const_mul bound
  apply majorantMember.mono'
  intro cell
  have coordinateNorm : ‖axisCoordinates parameters grade sequence cell‖ =
      axisWeight parameters grade cell * ‖sequence cell‖ := by
    unfold axisCoordinates
    rw [norm_smul, Real.norm_of_nonneg (axisWeight_pos parameters grade cell).le]
  rw [coordinateNorm]
  apply (dominated grade cell).trans
  exact le_abs_self _

/-! ### Bundled gradient traces -/

theorem scalarOriginGradient_mem (field : ACore parameters 1) :
    (fun cell => scalarOriginGradient field cell) ∈ axisCoreSubmodule parameters := by
  apply mem_axisCore_of_two_rows _ 3 diskSupConstant field field
  intro grade cell
  have gradientNorm : ‖scalarOriginGradient field cell‖ ≤
      ‖originPartial 0 (field.val cell)‖ + ‖originPartial 1 (field.val cell)‖ := by
    unfold scalarOriginGradient
    exact (planarPair_norm_le _ _).trans
      (add_le_add (PiLp.norm_apply_le _ 0) (PiLp.norm_apply_le _ 0))
  have firstTrace := crude_gradient_trace parameters (field.val cell) cell grade 0
  have secondTrace := crude_gradient_trace parameters (field.val cell) cell grade 1
  have weightNonneg := (axisWeight_pos parameters grade cell).le
  set rowNorm := ‖cellGradeRowLinear (grade := grade + 3) parameters cell (field.val cell)‖ with rowNormDef
  calc axisWeight parameters grade cell * ‖scalarOriginGradient field cell‖ ≤
      axisWeight parameters grade cell * (‖originPartial 0 (field.val cell)‖ +
        ‖originPartial 1 (field.val cell)‖) :=
        mul_le_mul_of_nonneg_left gradientNorm weightNonneg
    _ = axisWeight parameters grade cell * ‖originPartial 0 (field.val cell)‖ +
        axisWeight parameters grade cell * ‖originPartial 1 (field.val cell)‖ := by ring
    _ ≤ diskSupConstant * rowNorm + diskSupConstant * rowNorm :=
        add_le_add firstTrace secondTrace
    _ = diskSupConstant * (rowNorm + rowNorm) := by ring

theorem tangentialOriginGradient_mem (field : ACore parameters 3) :
    (fun cell => tangentialOriginGradient field cell) ∈ axisCoreSubmodule parameters := by
  apply mem_axisCore_of_two_rows _ 3 diskSupConstant field field
  intro grade cell
  have gradientNorm : ‖tangentialOriginGradient field cell‖ ≤
      ‖originPartial 0 (field.val cell)‖ + ‖originPartial 1 (field.val cell)‖ := by
    unfold tangentialOriginGradient
    exact (planarPair_norm_le _ _).trans
      (add_le_add (PiLp.norm_apply_le _ 1) (PiLp.norm_apply_le _ 1))
  have firstTrace := crude_gradient_trace parameters (field.val cell) cell grade 0
  have secondTrace := crude_gradient_trace parameters (field.val cell) cell grade 1
  have weightNonneg := (axisWeight_pos parameters grade cell).le
  set rowNorm := ‖cellGradeRowLinear (grade := grade + 3) parameters cell (field.val cell)‖ with rowNormDef
  calc axisWeight parameters grade cell * ‖tangentialOriginGradient field cell‖ ≤
      axisWeight parameters grade cell * (‖originPartial 0 (field.val cell)‖ +
        ‖originPartial 1 (field.val cell)‖) :=
        mul_le_mul_of_nonneg_left gradientNorm weightNonneg
    _ = axisWeight parameters grade cell * ‖originPartial 0 (field.val cell)‖ +
        axisWeight parameters grade cell * ‖originPartial 1 (field.val cell)‖ := by ring
    _ ≤ diskSupConstant * rowNorm + diskSupConstant * rowNorm :=
        add_le_add firstTrace secondTrace
    _ = diskSupConstant * (rowNorm + rowNorm) := by ring

/-- The direction extraction, bundled into the axis-data carrier. -/
def kappaData (direction : QuotientState parameters) : AxisData parameters :=
  (⟨fun cell => scalarOriginGradient (statePotential direction) cell,
      scalarOriginGradient_mem (statePotential direction)⟩,
    ⟨fun cell => tangentialOriginGradient (stateField direction) cell,
      tangentialOriginGradient_mem (stateField direction)⟩)

theorem kappaData_val (direction : QuotientState parameters) :
    ((kappaData direction).1.val, (kappaData direction).2.val) =
      kappaDirection direction := rfl

/-! ### The bundled source extraction -/

theorem sigmaExtraction_mem (Z : QuotientRows parameters) :
    (fun cell => sigmaExtraction Z cell) ∈ axisCoreSubmodule parameters := by
  apply mem_axisCore_of_two_rows _ 3 (2 * diskSupConstant) (Z 0) (Z 1)
  intro grade cell
  unfold sigmaExtraction
  set firstValue := originValue ((Z 0).val cell) 0 with firstValueDef
  set secondValue := originValue ((Z 1).val cell) 0 with secondValueDef
  have pairBound := planarPair_norm_le ((firstValue + secondValue) / 2)
    ((firstValue - secondValue) / (2 * Complex.I))
  have firstHalf : ‖(firstValue + secondValue) / 2‖ ≤ ‖firstValue‖ + ‖secondValue‖ := by
    rw [norm_div]
    have numerator := norm_add_le firstValue secondValue
    have denominator : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [denominator]
    linarith [norm_nonneg firstValue, norm_nonneg secondValue]
  have secondHalf : ‖(firstValue - secondValue) / (2 * Complex.I)‖ ≤
      ‖firstValue‖ + ‖secondValue‖ := by
    rw [norm_div]
    have numerator := norm_sub_le firstValue secondValue
    have denominator : ‖(2 : ℂ) * Complex.I‖ = 2 := by
      rw [norm_mul, Complex.norm_I, mul_one]
      norm_num
    rw [denominator]
    linarith [norm_nonneg firstValue, norm_nonneg secondValue]
  have firstComponent : ‖firstValue‖ ≤ ‖originValue ((Z 0).val cell)‖ := by
    rw [firstValueDef]
    exact PiLp.norm_apply_le _ 0
  have secondComponent : ‖secondValue‖ ≤ ‖originValue ((Z 1).val cell)‖ := by
    rw [secondValueDef]
    exact PiLp.norm_apply_le _ 0
  have firstTrace := crude_value_trace parameters ((Z 0).val cell) cell grade
  have secondTrace := crude_value_trace parameters ((Z 1).val cell) cell grade
  have firstRowMono := row_mono parameters cell ((Z 0).val cell)
    (by omega : grade + 2 ≤ grade + 3)
  have secondRowMono := row_mono parameters cell ((Z 1).val cell)
    (by omega : grade + 2 ≤ grade + 3)
  have weightNonneg := (axisWeight_pos parameters grade cell).le
  have pairNorm : ‖planarPair ((firstValue + secondValue) / 2) ((firstValue - secondValue) / (2 * Complex.I))‖ ≤ 2 * (‖originValue ((Z 0).val cell)‖ + ‖originValue ((Z 1).val cell)‖) := by
    calc ‖planarPair ((firstValue + secondValue) / 2) ((firstValue - secondValue) / (2 * Complex.I))‖ ≤ ‖(firstValue + secondValue) / 2‖ + ‖(firstValue - secondValue) / (2 * Complex.I)‖ := pairBound
      _ ≤ (‖firstValue‖ + ‖secondValue‖) + (‖firstValue‖ + ‖secondValue‖) :=
          add_le_add firstHalf secondHalf
      _ = 2 * (‖firstValue‖ + ‖secondValue‖) := by ring
      _ ≤ 2 * (‖originValue ((Z 0).val cell)‖ + ‖originValue ((Z 1).val cell)‖) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
          exact add_le_add firstComponent secondComponent
  calc axisWeight parameters grade cell * ‖planarPair ((firstValue + secondValue) / 2) ((firstValue - secondValue) / (2 * Complex.I))‖ ≤
      axisWeight parameters grade cell *
        (2 * (‖originValue ((Z 0).val cell)‖ + ‖originValue ((Z 1).val cell)‖)) :=
        mul_le_mul_of_nonneg_left pairNorm weightNonneg
    _ = 2 * (axisWeight parameters grade cell * ‖originValue ((Z 0).val cell)‖ +
        axisWeight parameters grade cell * ‖originValue ((Z 1).val cell)‖) := by ring
    _ ≤ 2 * (diskSupConstant * ‖cellGradeRowLinear (grade := grade + 2) parameters cell ((Z 0).val cell)‖ +
        diskSupConstant * ‖cellGradeRowLinear (grade := grade + 2) parameters cell ((Z 1).val cell)‖) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
        exact add_le_add firstTrace secondTrace
    _ ≤ 2 * (diskSupConstant * ‖cellGradeRowLinear (grade := grade + 3) parameters cell ((Z 0).val cell)‖ +
        diskSupConstant * ‖cellGradeRowLinear (grade := grade + 3) parameters cell ((Z 1).val cell)‖) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left firstRowMono diskSupConstant_pos.le
        · exact mul_le_mul_of_nonneg_left secondRowMono diskSupConstant_pos.le
    _ = 2 * diskSupConstant * (‖cellGradeRowLinear (grade := grade + 3) parameters cell ((Z 0).val cell)‖ + ‖cellGradeRowLinear (grade := grade + 3) parameters cell ((Z 1).val cell)‖) := by ring

/-- The bundled spin extraction. -/
def sigmaData (Z : QuotientRows parameters) : TCore parameters :=
  ⟨fun cell => sigmaExtraction Z cell, sigmaExtraction_mem Z⟩

theorem planarJ_mem (sequence : TCore parameters) :
    (fun cell => planarJPair (sequence.val cell)) ∈ axisCoreSubmodule parameters := by
  intro grade
  apply (sequence.property grade).mono'
  intro cell
  change ‖axisWeight parameters grade cell • planarJPair (sequence.val cell)‖ ≤
    ‖axisWeight parameters grade cell • sequence.val cell‖
  rw [norm_smul, norm_smul, planarJPair_norm]

/-- The bundled affine extraction, assembled from the spin extraction, the
cell derivative and the fourth-row gradient trace. -/
def etaData (cellLength : ℝ) (Z : QuotientRows parameters) : TCore parameters :=
  (Complex.ofReal cellLength)⁻¹ •
    (⟨fun cell => planarJPair
        (((⟨fun innerCell => scalarOriginGradient (Z 3) innerCell,
            scalarOriginGradient_mem (Z 3)⟩ : TCore parameters) +
          axisCellDerivative parameters (sigmaData Z)).val cell),
      planarJ_mem _⟩ : TCore parameters)

theorem etaData_val (cellLength : ℝ) (Z : QuotientRows parameters) (cell : ℤ) :
    (etaData cellLength Z).val cell = etaExtraction cellLength Z cell := by
  change (Complex.ofReal cellLength)⁻¹ • planarJPair
    (scalarOriginGradient (Z 3) cell +
      ((cell : ℂ) * Complex.I) • sigmaExtraction Z cell) = _
  rfl

/-- The bundled full source extraction `𝒥 Z` in the axis-data carrier. -/
def extractionData (cellLength : ℝ) (Z : QuotientRows parameters) : AxisData parameters :=
  (sigmaData Z, etaData cellLength Z)

theorem extractionData_val (cellLength : ℝ) (Z : QuotientRows parameters) :
    ((extractionData cellLength Z).1.val, (extractionData cellLength Z).2.val) =
      axisExtraction cellLength Z := by
  unfold extractionData axisExtraction
  apply Prod.ext
  · rfl
  · funext cell
    exact etaData_val cellLength Z cell

end Grad.AxisSplit
