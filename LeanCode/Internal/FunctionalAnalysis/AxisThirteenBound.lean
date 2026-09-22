import AxisExtractionBounds

noncomputable section

open scoped BigOperators

namespace Grad.AxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds

variable {parameters : PhaseParameters}

/-- The spin extraction of one cell against the two spin source values. -/
theorem sigmaExtraction_norm_le (Z : QuotientRows parameters) (cell : ℤ) :
    ‖sigmaExtraction Z cell‖ ≤
      2 * (‖originValue ((Z 0).val cell)‖ + ‖originValue ((Z 1).val cell)‖) := by
  set firstValue := originValue ((Z 0).val cell) 0 with firstValueDef
  set secondValue := originValue ((Z 1).val cell) 0 with secondValueDef
  have pairBound := planarPair_norm_le ((firstValue + secondValue) / 2)
    ((firstValue - secondValue) / (2 * Complex.I))
  have firstHalf : ‖(firstValue + secondValue) / 2‖ ≤ ‖firstValue‖ + ‖secondValue‖ := by
    rw [norm_div]
    have denominator : ‖(2 : ℂ)‖ = 2 := by norm_num
    have numerator := norm_add_le firstValue secondValue
    rw [denominator]
    linarith [norm_nonneg firstValue, norm_nonneg secondValue]
  have secondHalf : ‖(firstValue - secondValue) / (2 * Complex.I)‖ ≤
      ‖firstValue‖ + ‖secondValue‖ := by
    rw [norm_div]
    have denominator : ‖(2 : ℂ) * Complex.I‖ = 2 := by
      rw [norm_mul, Complex.norm_I, mul_one]
      norm_num
    have numerator := norm_sub_le firstValue secondValue
    rw [denominator]
    linarith [norm_nonneg firstValue, norm_nonneg secondValue]
  have firstComponent : ‖firstValue‖ ≤ ‖originValue ((Z 0).val cell)‖ := by
    rw [firstValueDef]
    exact PiLp.norm_apply_le _ 0
  have secondComponent : ‖secondValue‖ ≤ ‖originValue ((Z 1).val cell)‖ := by
    rw [secondValueDef]
    exact PiLp.norm_apply_le _ 0
  calc ‖sigmaExtraction Z cell‖ ≤
      ‖(firstValue + secondValue) / 2‖ + ‖(firstValue - secondValue) / (2 * Complex.I)‖ :=
        pairBound
    _ ≤ (‖firstValue‖ + ‖secondValue‖) + (‖firstValue‖ + ‖secondValue‖) :=
        add_le_add firstHalf secondHalf
    _ = 2 * (‖firstValue‖ + ‖secondValue‖) := by ring
    _ ≤ 2 * (‖originValue ((Z 0).val cell)‖ + ‖originValue ((Z 1).val cell)‖) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
        exact add_le_add firstComponent secondComponent

/-- The AL13 spin bound: one grade of value trace against the first two rows. -/
theorem sigmaData_grade_bound (Z : QuotientRows parameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) :
    axisGradeNorm parameters grade (sigmaData Z) ≤
      kappaTraceConstant *
        (originalGradeNorm (grade + 1) (Z 0) + originalGradeNorm (grade + 1) (Z 1)) := by
  have summed := axisGradeNorm_le_of_two_rows (sigmaData Z) grade
    (12 * Grad.CartesianState.diskSupConstant)
    (mul_nonneg (by norm_num) Grad.CartesianState.diskSupConstant_pos.le)
    (Z 0) (Z 1) (grade + 1) ?_
  · apply summed.trans
    unfold kappaTraceConstant
    apply le_of_eq
    ring
  intro cell
  have valueBound : ‖(sigmaData Z).val cell‖ ≤
      2 * (‖originValue ((Z 0).val cell)‖ + ‖originValue ((Z 1).val cell)‖) :=
    sigmaExtraction_norm_le Z cell
  have firstTrace := sharp_cell_value_trace parameters ((Z 0).val cell) cell grade
    gradePositive
  have secondTrace := sharp_cell_value_trace parameters ((Z 1).val cell) cell grade
    gradePositive
  calc axisWeight parameters grade cell * ‖(sigmaData Z).val cell‖ ≤
      axisWeight parameters grade cell *
        (2 * (‖originValue ((Z 0).val cell)‖ + ‖originValue ((Z 1).val cell)‖)) :=
        mul_le_mul_of_nonneg_left valueBound (axisWeight_pos parameters grade cell).le
    _ = 2 * (axisWeight parameters grade cell * ‖originValue ((Z 0).val cell)‖ +
        axisWeight parameters grade cell * ‖originValue ((Z 1).val cell)‖) := by ring
    _ ≤ 2 * (6 * Grad.CartesianState.diskSupConstant *
          ‖cellGradeRowLinear (grade := grade + 1) parameters cell ((Z 0).val cell)‖ +
        6 * Grad.CartesianState.diskSupConstant *
          ‖cellGradeRowLinear (grade := grade + 1) parameters cell ((Z 1).val cell)‖) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
        exact add_le_add firstTrace secondTrace
    _ = 12 * Grad.CartesianState.diskSupConstant *
        (‖cellGradeRowLinear (grade := grade + 1) parameters cell ((Z 0).val cell)‖ +
          ‖cellGradeRowLinear (grade := grade + 1) parameters cell ((Z 1).val cell)‖) := by
        ring

/-- The planar rotation preserves every axis grade norm. -/
theorem axisGradeNorm_planarJ (sequence : TCore parameters) (grade : ℕ) :
    axisGradeNorm parameters grade
        (⟨fun cell => planarJPair (sequence.val cell), planarJ_mem sequence⟩ :
          TCore parameters) =
      axisGradeNorm parameters grade sequence := by
  apply le_antisymm
  · unfold axisGradeNorm
    apply lp.norm_mono (by norm_num)
    intro cell
    change ‖axisWeight parameters grade cell • planarJPair (sequence.val cell)‖ ≤
      ‖axisWeight parameters grade cell • sequence.val cell‖
    rw [norm_smul, norm_smul, planarJPair_norm]
  · unfold axisGradeNorm
    apply lp.norm_mono (by norm_num)
    intro cell
    change ‖axisWeight parameters grade cell • sequence.val cell‖ ≤
      ‖axisWeight parameters grade cell • planarJPair (sequence.val cell)‖
    rw [norm_smul, norm_smul, planarJPair_norm]

/-- The AL13 constant `C_{q,L}`, depending only on the fixed supremum
constant and the cell length. -/
def extractionBoundConstant (cellLength : ℝ) : ℝ :=
  3 * kappaTraceConstant * (1 + |cellLength|⁻¹)

theorem extractionBoundConstant_nonneg (cellLength : ℝ) :
    0 ≤ extractionBoundConstant cellLength :=
  mul_nonneg (mul_nonneg (by norm_num) kappaTraceConstant_nonneg) (by positivity)

/-- AL13 at the coefficient-core level: the full axis extraction pays
exactly three grades, with the literal `T^{q+1}` data norms on both
components and the four-row source norm. -/
theorem extractionData_bound (cellLength : ℝ) (Z : QuotientRows parameters) (grade : ℕ) :
    axisDataNorm parameters grade (extractionData cellLength Z) ≤
      extractionBoundConstant cellLength * rowsGradeNorm (grade + 3) Z := by
  have rowNonneg : ∀ row : Fin 4, 0 ≤ originalGradeNorm (grade + 3) (Z row) :=
    fun row => originalGradeNorm_nonnegative _ _
  have rowLe : ∀ row : Fin 4, originalGradeNorm (grade + 3) (Z row) ≤
      rowsGradeNorm (grade + 3) Z := by
    intro row
    unfold rowsGradeNorm
    exact Finset.single_le_sum (fun inner _ => originalGradeNorm_nonnegative _ _)
      (Finset.mem_univ row)
  have sigmaBound : axisGradeNorm parameters (grade + 1) (sigmaData Z) ≤
      kappaTraceConstant * (2 * rowsGradeNorm (grade + 3) Z) := by
    have base := sigmaData_grade_bound Z (grade + 1) (by omega)
    apply base.trans
    apply mul_le_mul_of_nonneg_left _ kappaTraceConstant_nonneg
    have firstMono : originalGradeNorm (grade + 1 + 1) (Z 0) ≤
        originalGradeNorm (grade + 3) (Z 0) :=
      originalGradeNorm_mono (by omega) (Z 0)
    have secondMono : originalGradeNorm (grade + 1 + 1) (Z 1) ≤
        originalGradeNorm (grade + 3) (Z 1) :=
      originalGradeNorm_mono (by omega) (Z 1)
    calc originalGradeNorm (grade + 1 + 1) (Z 0) + originalGradeNorm (grade + 1 + 1) (Z 1) ≤
        originalGradeNorm (grade + 3) (Z 0) + originalGradeNorm (grade + 3) (Z 1) :=
          add_le_add firstMono secondMono
      _ ≤ rowsGradeNorm (grade + 3) Z + rowsGradeNorm (grade + 3) Z :=
          add_le_add (rowLe 0) (rowLe 1)
      _ = 2 * rowsGradeNorm (grade + 3) Z := by ring
  have sigmaShiftBound : axisGradeNorm parameters (grade + 2) (sigmaData Z) ≤
      kappaTraceConstant * (2 * rowsGradeNorm (grade + 3) Z) := by
    have base := sigmaData_grade_bound Z (grade + 2) (by omega)
    apply base.trans
    apply mul_le_mul_of_nonneg_left _ kappaTraceConstant_nonneg
    calc originalGradeNorm (grade + 2 + 1) (Z 0) + originalGradeNorm (grade + 2 + 1) (Z 1) =
        originalGradeNorm (grade + 3) (Z 0) + originalGradeNorm (grade + 3) (Z 1) := by
          have gradeEq : grade + 2 + 1 = grade + 3 := by omega
          rw [gradeEq]
      _ ≤ rowsGradeNorm (grade + 3) Z + rowsGradeNorm (grade + 3) Z :=
          add_le_add (rowLe 0) (rowLe 1)
      _ = 2 * rowsGradeNorm (grade + 3) Z := by ring
  set gradThree : TCore parameters :=
    ⟨fun innerCell => scalarOriginGradient (Z 3) innerCell,
      scalarOriginGradient_mem (Z 3)⟩ with gradThreeDef
  have gradientBound : axisGradeNorm parameters (grade + 1) gradThree ≤
      kappaTraceConstant * rowsGradeNorm (grade + 3) Z := by
    have base := scalarGradient_grade_bound (Z 3) (grade + 1) (by omega)
    rw [← gradThreeDef] at base
    apply base.trans
    apply mul_le_mul_of_nonneg_left _ kappaTraceConstant_nonneg
    have gradeEq : grade + 1 + 2 = grade + 3 := by omega
    rw [gradeEq]
    exact rowLe 3
  have etaBound : axisGradeNorm parameters (grade + 1) (etaData cellLength Z) ≤
      |cellLength|⁻¹ * (kappaTraceConstant * (3 * rowsGradeNorm (grade + 3) Z)) := by
    unfold etaData
    rw [axisGradeNorm_smul]
    have scalarNorm : ‖((cellLength : ℂ))⁻¹‖ = |cellLength|⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
    rw [scalarNorm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [axisGradeNorm_planarJ]
    apply (axisGradeNorm_add_le parameters (grade + 1) _ _).trans
    have derivativeBound : axisGradeNorm parameters (grade + 1)
        (axisCellDerivative parameters (sigmaData Z)) ≤
        kappaTraceConstant * (2 * rowsGradeNorm (grade + 3) Z) :=
      (axisCellDerivative_bound parameters (grade + 1) (sigmaData Z)).trans sigmaShiftBound
    calc axisGradeNorm parameters (grade + 1) gradThree +
        axisGradeNorm parameters (grade + 1)
          (axisCellDerivative parameters (sigmaData Z)) ≤
        kappaTraceConstant * rowsGradeNorm (grade + 3) Z +
          kappaTraceConstant * (2 * rowsGradeNorm (grade + 3) Z) :=
          add_le_add gradientBound derivativeBound
      _ = kappaTraceConstant * (3 * rowsGradeNorm (grade + 3) Z) := by ring
  have rowsNonneg : 0 ≤ rowsGradeNorm (grade + 3) Z := rowsGradeNorm_nonneg _ _
  calc axisDataNorm parameters grade (extractionData cellLength Z) =
      axisGradeNorm parameters (grade + 1) (sigmaData Z) +
        axisGradeNorm parameters (grade + 1) (etaData cellLength Z) := rfl
    _ ≤ kappaTraceConstant * (2 * rowsGradeNorm (grade + 3) Z) +
        |cellLength|⁻¹ * (kappaTraceConstant * (3 * rowsGradeNorm (grade + 3) Z)) :=
        add_le_add sigmaBound etaBound
    _ ≤ kappaTraceConstant * (3 * rowsGradeNorm (grade + 3) Z) +
        |cellLength|⁻¹ * (kappaTraceConstant * (3 * rowsGradeNorm (grade + 3) Z)) := by
        apply add_le_add _ le_rfl
        apply mul_le_mul_of_nonneg_left _ kappaTraceConstant_nonneg
        linarith
    _ = extractionBoundConstant cellLength * rowsGradeNorm (grade + 3) Z := by
        unfold extractionBoundConstant
        ring

end Grad.AxisSplit
