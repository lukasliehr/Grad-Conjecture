import AxisSharpTrace

noncomputable section

open scoped BigOperators

namespace Grad.AxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.NonlinearRadial

variable {parameters : PhaseParameters}

/-- The shifted supremum indices inside the grade-`(g+2)` index set, `g ≥ 1`. -/
def sharpShiftIndex (grade : ℕ) (gradePositive : 1 ≤ grade) (direction : Fin 2)
    (slot : Fin 6) : GradeMultiIndex (grade + 2) :=
  ⟨(⟨(diskSupMultiIndex slot).1 + (if direction = 0 then 1 else 0), by
      have componentLe := (diskSupIndex_component_le slot).1
      by_cases directionZero : direction = 0
      · rw [if_pos directionZero]
        omega
      · rw [if_neg directionZero]
        omega⟩,
    ⟨(diskSupMultiIndex slot).2 + (if direction = 1 then 1 else 0), by
      have componentLe := (diskSupIndex_component_le slot).2
      by_cases directionOne : direction = 1
      · rw [if_pos directionOne]
        omega
      · rw [if_neg directionOne]
        omega⟩), by
    have orderLe := diskSupMultiIndex_order_le_two slot
    change (diskSupMultiIndex slot).1 + (if direction = 0 then 1 else 0) +
      ((diskSupMultiIndex slot).2 + (if direction = 1 then 1 else 0)) ≤ grade + 2
    unfold cartesianOrder at orderLe
    by_cases directionZero : direction = 0
    · rw [if_pos directionZero, if_neg (by rw [directionZero]; decide)]
      omega
    · have directionOne : direction = 1 := by omega
      rw [if_neg directionZero, if_pos directionOne]
      omega⟩

theorem sharpShiftIndex_toCartesian (grade : ℕ) (gradePositive : 1 ≤ grade)
    (direction : Fin 2) (slot : Fin 6) :
    (sharpShiftIndex grade gradePositive direction slot).toCartesian =
      shiftedCartesianIndex (fun _ : Fin 1 => direction) (diskSupMultiIndex slot) := by
  rw [shiftedCartesianIndex_single]
  rfl

theorem sharpShiftIndex_order (grade : ℕ) (gradePositive : 1 ≤ grade)
    (direction : Fin 2) (slot : Fin 6) :
    cartesianOrder (sharpShiftIndex grade gradePositive direction slot).toCartesian =
      cartesianOrder (diskSupMultiIndex slot) + 1 := by
  rw [sharpShiftIndex_toCartesian, shiftedCartesianIndex_order]

/-- M27's sharp gradient trace: two grades against the weighted row. -/
theorem sharp_cell_gradient_trace {dimension : ℕ} (parameters : PhaseParameters)
    (field : ClosedJet dimension) (cell : ℤ) (grade : ℕ) (gradePositive : 1 ≤ grade)
    (direction : Fin 2) :
    axisWeight parameters grade cell * ‖originPartial direction field‖ ≤
      6 * diskSupConstant *
        ‖cellGradeRowLinear (grade := grade + 2) parameters cell field‖ := by
  set lambda := cellFrequency cell with lambdaDef
  have lambdaOne : 1 ≤ lambda := cellFrequency_one_le cell
  have lambdaPos : 0 < lambda := cellFrequency_pos cell
  have inverse_pos : 0 < lambda⁻¹ := inv_pos.mpr lambdaPos
  have inverse_le : lambda⁻¹ ≤ 1 := inv_le_one_of_one_le₀ lambdaOne
  have valueIdentity : axisWeight parameters grade cell * ‖originPartial direction field‖ =
      lambda ^ grade *
        ‖originValue (partialJet direction (phaseWeightedJet parameters cell field))‖ := by
    rw [show originValue (partialJet direction (phaseWeightedJet parameters cell field)) =
      originPartial direction (phaseWeightedJet parameters cell field) from rfl]
    rw [phaseWeightedJet_originPartial, norm_smul,
      Real.norm_of_nonneg (cartesianWeight_pos parameters cell _).le,
      axisWeight_eq_weight_origin]
    ring
  rw [valueIdentity]
  have sharpBound := sharp_origin_value inverse_pos inverse_le
    (partialJet direction (phaseWeightedJet parameters cell field))
  have termBound : ∀ slot : Fin 6,
      lambda ^ grade * ((lambda⁻¹) ^ cartesianOrder (diskSupMultiIndex slot) *
        (lambda⁻¹)⁻¹ *
        ‖closedContinuousToDiskL2 (closedMultiDerivative
          (partialJet direction (phaseWeightedJet parameters cell field))
          (diskSupMultiIndex slot))‖) ≤
      ‖cellGradeRowLinear (grade := grade + 2) parameters cell field‖ := by
    intro slot
    have orderLe := diskSupMultiIndex_order_le_two slot
    set order := cartesianOrder (diskSupMultiIndex slot) with orderDef
    have wordShift : closedMultiDerivative
        (partialJet direction (phaseWeightedJet parameters cell field))
        (diskSupMultiIndex slot) =
        closedMultiDerivative (phaseWeightedJet parameters cell field)
          ((sharpShiftIndex grade gradePositive direction slot).toCartesian) := by
      rw [sharpShiftIndex_toCartesian]
      exact shiftedClosedJet_closedMultiDerivative
        (phaseWeightedJet parameters cell field) (fun _ : Fin 1 => direction)
        (diskSupMultiIndex slot)
    have rowTerm := row_term_le parameters cell field (grade + 2)
      (sharpShiftIndex grade gradePositive direction slot)
    have shiftOrder := sharpShiftIndex_order grade gradePositive direction slot
    rw [shiftOrder, ← orderDef] at rowTerm
    have powerIdentity : lambda ^ grade * ((lambda⁻¹) ^ order * (lambda⁻¹)⁻¹) =
        lambda ^ (grade + 2 - (order + 1)) := by
      rw [inv_inv, inv_pow]
      have split : lambda ^ (grade + 2 - (order + 1)) * lambda ^ order =
          lambda ^ (grade + 1) := by
        rw [← pow_add]
        congr 1
        omega
      have powNe : lambda ^ order ≠ 0 := pow_ne_zero order lambdaPos.ne'
      field_simp
      rw [← pow_succ]
      linarith [split]
    calc lambda ^ grade * ((lambda⁻¹) ^ order * (lambda⁻¹)⁻¹ *
        ‖closedContinuousToDiskL2 (closedMultiDerivative
          (partialJet direction (phaseWeightedJet parameters cell field))
          (diskSupMultiIndex slot))‖) =
        lambda ^ (grade + 2 - (order + 1)) *
        ‖closedContinuousToDiskL2 (closedMultiDerivative
          (phaseWeightedJet parameters cell field)
          ((sharpShiftIndex grade gradePositive direction slot).toCartesian))‖ := by
          rw [← powerIdentity, wordShift]
          ring
      _ ≤ ‖cellGradeRowLinear (grade := grade + 2) parameters cell field‖ := rowTerm
  calc lambda ^ grade *
      ‖originValue (partialJet direction (phaseWeightedJet parameters cell field))‖ ≤
      lambda ^ grade * (diskSupConstant * scaledSupContent lambda⁻¹
        (partialJet direction (phaseWeightedJet parameters cell field))) :=
        mul_le_mul_of_nonneg_left sharpBound (pow_nonneg lambdaPos.le _)
    _ = diskSupConstant * ∑ slot : Fin 6, lambda ^ grade *
        ((lambda⁻¹) ^ cartesianOrder (diskSupMultiIndex slot) * (lambda⁻¹)⁻¹ *
        ‖closedContinuousToDiskL2 (closedMultiDerivative
          (partialJet direction (phaseWeightedJet parameters cell field))
          (diskSupMultiIndex slot))‖) := by
        unfold scaledSupContent
        rw [← mul_assoc, mul_comm (lambda ^ grade) diskSupConstant, mul_assoc,
          Finset.mul_sum]
    _ ≤ diskSupConstant * ∑ _slot : Fin 6,
        ‖cellGradeRowLinear (grade := grade + 2) parameters cell field‖ := by
        apply mul_le_mul_of_nonneg_left _ diskSupConstant_pos.le
        exact Finset.sum_le_sum (fun slot _ => termBound slot)
    _ = 6 * diskSupConstant *
        ‖cellGradeRowLinear (grade := grade + 2) parameters cell field‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring

end Grad.AxisSplit
