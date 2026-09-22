import AxisSplitConsumer

noncomputable section

open scoped BigOperators

namespace Grad.AxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.NonlinearRadial

variable {parameters : PhaseParameters}

/-! ### The frequency-scaled disk supremum through the exact dilation -/

theorem dilationPoint_origin {scale : ℝ} (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1) :
    dilationPoint scale nonnegative bounded originPoint = originPoint := by
  apply Subtype.ext
  change scale • originPoint.val = originPoint.val
  rw [originPoint_val, smul_zero]

theorem dilationJet_originValue {dimension : ℕ} {scale : ℝ}
    (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1) (field : ClosedJet dimension) :
    originValue (dilationJet scale field) = originValue field := by
  unfold originValue
  rw [dilationJet_value_closed nonnegative bounded, dilationPoint_origin]

theorem l2_real_smul {dimension : ℕ} (scalar : ℝ)
    (field : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) :
    ‖closedContinuousToDiskL2 (scalar • field)‖ = |scalar| * ‖closedContinuousToDiskL2 field‖ := by
  have coeSmul : scalar • field = (scalar : ℂ) • field := by
    apply ContinuousMap.ext
    intro point
    exact (Complex.coe_smul scalar (field point)).symm
  rw [coeSmul, closedContinuousToDiskL2_smul, norm_smul, Complex.norm_real,
    Real.norm_eq_abs]

/-- One dilated derivative word against the original word. -/
theorem dilation_word_l2_le {dimension : ℕ} {scale : ℝ}
    (positive : 0 < scale) (bounded : scale ≤ 1) (field : ClosedJet dimension)
    (index : CartesianMultiIndex) :
    ‖closedContinuousToDiskL2 (closedMultiDerivative (dilationJet scale field) index)‖ ≤
      scale ^ cartesianOrder index * scale⁻¹ *
        ‖closedContinuousToDiskL2 (closedMultiDerivative field index)‖ := by
  have wordIdentity : closedMultiDerivative (dilationJet scale field) index =
      (scale ^ cartesianOrder index) •
        ((closedMultiDerivative field index).comp
          (dilationClosedMap scale positive.le bounded)) := by
    apply ContinuousMap.ext
    intro point
    change closedDerivative (dilationJet scale field) (cartesianOrder index)
      (cartesianMultiIndexWord index) point = _
    rw [dilationJet_derivative positive.le bounded field (cartesianMultiIndexWord index)
      point]
    rfl
  rw [wordIdentity, l2_real_smul, abs_of_nonneg (pow_nonneg positive.le _), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg positive.le _)
  exact closedValueL2_dilation_bound positive bounded (closedMultiDerivative field index)

/-- The scaled disk-supremum content at one dilation scale. -/
def scaledSupContent {dimension : ℕ} (scale : ℝ) (field : ClosedJet dimension) : ℝ :=
  ∑ slot : Fin 6, scale ^ cartesianOrder (diskSupMultiIndex slot) * scale⁻¹ *
    ‖closedContinuousToDiskL2 (closedMultiDerivative field (diskSupMultiIndex slot))‖

theorem scaledSupContent_nonneg {dimension : ℕ} {scale : ℝ} (positive : 0 < scale)
    (field : ClosedJet dimension) : 0 ≤ scaledSupContent scale field := by
  apply Finset.sum_nonneg
  intro slot _
  have factorNonneg : (0 : ℝ) ≤ scale ^ cartesianOrder (diskSupMultiIndex slot) * scale⁻¹ :=
    mul_nonneg (pow_nonneg positive.le _) (inv_nonneg.mpr positive.le)
  exact mul_nonneg factorNonneg (norm_nonneg _)

/-- The sharp frequency-scaled axis value bound: dilating by `scale` before
the fixed supremum estimate pays `scale⁻¹` on the value, one on the first
derivatives, and `scale` on the second derivatives. -/
theorem sharp_origin_value {dimension : ℕ} {scale : ℝ}
    (positive : 0 < scale) (bounded : scale ≤ 1) (field : ClosedJet dimension) :
    ‖originValue field‖ ≤ diskSupConstant * scaledSupContent scale field := by
  rw [← dilationJet_originValue positive.le bounded field]
  have supBound := diskSup_bound (dilationJet scale field) originPoint
  apply supBound.trans
  apply mul_le_mul_of_nonneg_left _ diskSupConstant_pos.le
  have energyLe : Real.sqrt (diskSupEnergy (dilationJet scale field)) ≤
      scaledSupContent scale field := by
    have sumSquares : diskSupEnergy (dilationJet scale field) ≤
        (scaledSupContent scale field) ^ 2 := by
      unfold diskSupEnergy scaledSupContent
      calc (∑ slot : Fin 6, ‖closedDerivativeL2 (diskSupMultiIndex slot)
            (dilationJet scale field)‖ ^ 2) ≤
          ∑ slot : Fin 6, (scale ^ cartesianOrder (diskSupMultiIndex slot) * scale⁻¹ *
            ‖closedContinuousToDiskL2 (closedMultiDerivative field
              (diskSupMultiIndex slot))‖) ^ 2 := by
            apply Finset.sum_le_sum
            intro slot _
            apply pow_le_pow_left₀ (norm_nonneg _)
            exact dilation_word_l2_le positive bounded field (diskSupMultiIndex slot)
        _ ≤ (∑ slot : Fin 6, scale ^ cartesianOrder (diskSupMultiIndex slot) * scale⁻¹ *
            ‖closedContinuousToDiskL2 (closedMultiDerivative field
              (diskSupMultiIndex slot))‖) ^ 2 := by
            rw [sq (∑ slot : Fin 6, scale ^ cartesianOrder (diskSupMultiIndex slot) *
              scale⁻¹ * ‖closedContinuousToDiskL2 (closedMultiDerivative field
                (diskSupMultiIndex slot))‖), Finset.sum_mul]
            apply Finset.sum_le_sum
            intro slot _
            rw [sq]
            have termNonneg : (0 : ℝ) ≤ scale ^ cartesianOrder (diskSupMultiIndex slot) *
                scale⁻¹ * ‖closedContinuousToDiskL2 (closedMultiDerivative field
                  (diskSupMultiIndex slot))‖ :=
              mul_nonneg (mul_nonneg (pow_nonneg positive.le _)
                (inv_nonneg.mpr positive.le)) (norm_nonneg _)
            apply mul_le_mul_of_nonneg_left _ termNonneg
            apply Finset.single_le_sum (fun inner _ => ?_) (Finset.mem_univ slot)
            exact mul_nonneg (mul_nonneg (pow_nonneg positive.le _)
              (inv_nonneg.mpr positive.le)) (norm_nonneg _)
    have sqrtStep := Real.sqrt_le_sqrt sumSquares
    rwa [Real.sqrt_sq (scaledSupContent_nonneg positive field)] at sqrtStep
  exact energyLe

/-! ### The exact one- and two-grade cell traces -/

/-- The six supremum indices inside the grade-`(g+1)` index set, `g ≥ 1`. -/
def sharpSupIndex (grade : ℕ) (gradePositive : 1 ≤ grade) (slot : Fin 6) :
    GradeMultiIndex (grade + 1) :=
  ⟨(⟨(diskSupMultiIndex slot).1, by
      have componentLe := (diskSupIndex_component_le slot).1
      omega⟩,
    ⟨(diskSupMultiIndex slot).2, by
      have componentLe := (diskSupIndex_component_le slot).2
      omega⟩), by
    have orderLe := diskSupMultiIndex_order_le_two slot
    change (diskSupMultiIndex slot).1 + (diskSupMultiIndex slot).2 ≤ grade + 1
    unfold cartesianOrder at orderLe
    omega⟩

theorem sharpSupIndex_toCartesian (grade : ℕ) (gradePositive : 1 ≤ grade) (slot : Fin 6) :
    (sharpSupIndex grade gradePositive slot).toCartesian = diskSupMultiIndex slot := rfl

/-- One grade-row term dominates each weighted supremum word. -/
theorem row_term_le {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) (targetGrade : ℕ) (index : GradeMultiIndex targetGrade) :
    cellFrequency cell ^ (targetGrade - cartesianOrder index.toCartesian) *
        ‖closedContinuousToDiskL2 (closedMultiDerivative
          (phaseWeightedJet parameters cell field) index.toCartesian)‖ ≤
      ‖cellGradeRowLinear (grade := targetGrade) parameters cell field‖ := by
  have squares : (cellFrequency cell ^ (targetGrade - cartesianOrder index.toCartesian) *
      ‖closedContinuousToDiskL2 (closedMultiDerivative
        (phaseWeightedJet parameters cell field) index.toCartesian)‖) ^ 2 ≤
      ‖cellGradeRowLinear (grade := targetGrade) parameters cell field‖ ^ 2 := by
    rw [cellGradeRow_norm_sq]
    have termShape : (cellFrequency cell ^ (targetGrade - cartesianOrder index.toCartesian) *
        ‖closedContinuousToDiskL2 (closedMultiDerivative
          (phaseWeightedJet parameters cell field) index.toCartesian)‖) ^ 2 =
        cellFrequency cell ^ (2 * (targetGrade - cartesianOrder index.toCartesian)) *
        ‖closedContinuousToDiskL2 (closedMultiDerivative
          (phaseWeightedJet parameters cell field) index.toCartesian)‖ ^ 2 := by
      rw [mul_pow, ← pow_mul, mul_comm 2 (targetGrade - cartesianOrder index.toCartesian)]
    rw [termShape]
    apply Finset.single_le_sum (f := fun inner : GradeMultiIndex targetGrade =>
      cellFrequency cell ^ (2 * (targetGrade - cartesianOrder inner.toCartesian)) *
      ‖closedContinuousToDiskL2 (closedMultiDerivative
        (phaseWeightedJet parameters cell field) inner.toCartesian)‖ ^ 2)
      (fun inner _ => mul_nonneg (pow_nonneg (cellFrequency_pos cell).le _) (sq_nonneg _))
      (Finset.mem_univ index)
  have leftNonneg : 0 ≤ cellFrequency cell ^
      (targetGrade - cartesianOrder index.toCartesian) *
      ‖closedContinuousToDiskL2 (closedMultiDerivative
        (phaseWeightedJet parameters cell field) index.toCartesian)‖ :=
    mul_nonneg (pow_nonneg (cellFrequency_pos cell).le _) (norm_nonneg _)
  have sqrtStep := Real.sqrt_le_sqrt squares
  rwa [Real.sqrt_sq leftNonneg, Real.sqrt_sq (norm_nonneg _)] at sqrtStep

/-- M27's sharp value trace: one grade against the weighted row. -/
theorem sharp_cell_value_trace {dimension : ℕ} (parameters : PhaseParameters)
    (field : ClosedJet dimension) (cell : ℤ) (grade : ℕ) (gradePositive : 1 ≤ grade) :
    axisWeight parameters grade cell * ‖originValue field‖ ≤
      6 * diskSupConstant *
        ‖cellGradeRowLinear (grade := grade + 1) parameters cell field‖ := by
  set lambda := cellFrequency cell with lambdaDef
  have lambdaOne : 1 ≤ lambda := cellFrequency_one_le cell
  have lambdaPos : 0 < lambda := cellFrequency_pos cell
  have inverse_pos : 0 < lambda⁻¹ := inv_pos.mpr lambdaPos
  have inverse_le : lambda⁻¹ ≤ 1 := inv_le_one_of_one_le₀ lambdaOne
  have valueIdentity : axisWeight parameters grade cell * ‖originValue field‖ =
      lambda ^ grade * ‖originValue (phaseWeightedJet parameters cell field)‖ := by
    rw [phaseWeightedJet_originValue, norm_smul,
      Real.norm_of_nonneg (cartesianWeight_pos parameters cell _).le,
      axisWeight_eq_weight_origin]
    ring
  rw [valueIdentity]
  have sharpBound := sharp_origin_value inverse_pos inverse_le
    (phaseWeightedJet parameters cell field)
  have termBound : ∀ slot : Fin 6,
      lambda ^ grade * ((lambda⁻¹) ^ cartesianOrder (diskSupMultiIndex slot) *
        (lambda⁻¹)⁻¹ *
        ‖closedContinuousToDiskL2 (closedMultiDerivative
          (phaseWeightedJet parameters cell field) (diskSupMultiIndex slot))‖) ≤
      ‖cellGradeRowLinear (grade := grade + 1) parameters cell field‖ := by
    intro slot
    have orderLe := diskSupMultiIndex_order_le_two slot
    set order := cartesianOrder (diskSupMultiIndex slot) with orderDef
    have powerIdentity : lambda ^ grade * ((lambda⁻¹) ^ order * (lambda⁻¹)⁻¹) =
        lambda ^ (grade + 1 - order) := by
      rw [inv_inv, inv_pow]
      have split : lambda ^ (grade + 1 - order) * lambda ^ order = lambda ^ (grade + 1) := by
        rw [← pow_add, Nat.sub_add_cancel (by omega : order ≤ grade + 1)]
      have powNe : lambda ^ order ≠ 0 := pow_ne_zero order lambdaPos.ne'
      field_simp
      rw [← pow_succ]
      linarith [split]
    have rowTerm := row_term_le parameters cell field (grade + 1)
      (sharpSupIndex grade gradePositive slot)
    rw [sharpSupIndex_toCartesian] at rowTerm
    calc lambda ^ grade * ((lambda⁻¹) ^ order * (lambda⁻¹)⁻¹ *
        ‖closedContinuousToDiskL2 (closedMultiDerivative
          (phaseWeightedJet parameters cell field) (diskSupMultiIndex slot))‖) =
        lambda ^ (grade + 1 - order) *
        ‖closedContinuousToDiskL2 (closedMultiDerivative
          (phaseWeightedJet parameters cell field) (diskSupMultiIndex slot))‖ := by
          rw [← powerIdentity]
          ring
      _ ≤ ‖cellGradeRowLinear (grade := grade + 1) parameters cell field‖ := rowTerm
  calc lambda ^ grade * ‖originValue (phaseWeightedJet parameters cell field)‖ ≤
      lambda ^ grade * (diskSupConstant *
        scaledSupContent lambda⁻¹ (phaseWeightedJet parameters cell field)) :=
        mul_le_mul_of_nonneg_left sharpBound (pow_nonneg lambdaPos.le _)
    _ = diskSupConstant * ∑ slot : Fin 6, lambda ^ grade *
        ((lambda⁻¹) ^ cartesianOrder (diskSupMultiIndex slot) * (lambda⁻¹)⁻¹ *
        ‖closedContinuousToDiskL2 (closedMultiDerivative
          (phaseWeightedJet parameters cell field) (diskSupMultiIndex slot))‖) := by
        unfold scaledSupContent
        rw [← mul_assoc, mul_comm (lambda ^ grade) diskSupConstant, mul_assoc,
          Finset.mul_sum]
    _ ≤ diskSupConstant * ∑ _slot : Fin 6,
        ‖cellGradeRowLinear (grade := grade + 1) parameters cell field‖ := by
        apply mul_le_mul_of_nonneg_left _ diskSupConstant_pos.le
        exact Finset.sum_le_sum (fun slot _ => termBound slot)
    _ = 6 * diskSupConstant *
        ‖cellGradeRowLinear (grade := grade + 1) parameters cell field‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring

end Grad.AxisSplit
