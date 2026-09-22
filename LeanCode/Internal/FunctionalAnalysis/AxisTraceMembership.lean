import AxisLift

noncomputable section

open scoped BigOperators ContDiff
open MeasureTheory

namespace Grad.AxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds

variable {parameters : PhaseParameters}

/-! ### Crude per-cell trace bounds through the fixed disk supremum -/

theorem diskSupIndex_component_le (slot : Fin 6) :
    (diskSupMultiIndex slot).1 ≤ 2 ∧
      (diskSupMultiIndex slot).2 ≤ 2 := by
  fin_cases slot <;> exact ⟨by decide, by decide⟩

/-- The six supremum indices, lifted into the grade-`(g+2)` index set. -/
def liftedSupIndex (grade : ℕ) (slot : Fin 6) : GradeMultiIndex (grade + 2) :=
  ⟨(⟨(diskSupMultiIndex slot).1, by
      have componentLe := (diskSupIndex_component_le slot).1
      omega⟩,
    ⟨(diskSupMultiIndex slot).2, by
      have componentLe := (diskSupIndex_component_le slot).2
      omega⟩), by
    have orderLe := diskSupMultiIndex_order_le_two slot
    change (diskSupMultiIndex slot).1 +
      (diskSupMultiIndex slot).2 ≤ grade + 2
    unfold cartesianOrder at orderLe
    omega⟩

theorem liftedSupIndex_toCartesian (grade : ℕ) (slot : Fin 6) :
    (liftedSupIndex grade slot).toCartesian = diskSupMultiIndex slot := rfl

theorem diskSupMultiIndex_injective :
    Function.Injective diskSupMultiIndex := by
  intro first second equal
  fin_cases first <;> fin_cases second <;>
    first | rfl | (exact absurd equal (by decide))

theorem liftedSupIndex_injective (grade : ℕ) :
    Function.Injective (liftedSupIndex grade) := by
  intro first second equal
  apply diskSupMultiIndex_injective
  have firstComponents := congrArg (fun index : GradeMultiIndex (grade + 2) =>
    index.val.1.val) equal
  have secondComponents := congrArg (fun index : GradeMultiIndex (grade + 2) =>
    index.val.2.val) equal
  exact Prod.ext firstComponents secondComponents

/-- The disk supremum energy of a weighted jet against the grade row. -/
theorem supEnergy_le_row {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) (grade : ℕ) :
    cellFrequency cell ^ grade *
        Real.sqrt (diskSupEnergy (phaseWeightedJet parameters cell field)) ≤
      ‖cellGradeRowLinear (grade := grade + 2) parameters cell field‖ := by
  have powNonneg : (0 : ℝ) ≤ cellFrequency cell ^ grade :=
    pow_nonneg (cellFrequency_pos cell).le grade
  rw [show cellFrequency cell ^ grade *
      Real.sqrt (diskSupEnergy (phaseWeightedJet parameters cell field)) =
      Real.sqrt ((cellFrequency cell ^ grade) ^ 2 *
        diskSupEnergy (phaseWeightedJet parameters cell field)) from by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq powNonneg]]
  rw [show ‖cellGradeRowLinear (grade := grade + 2) parameters cell field‖ =
      Real.sqrt (‖cellGradeRowLinear (grade := grade + 2) parameters cell field‖ ^ 2) from
    (Real.sqrt_sq (norm_nonneg _)).symm]
  apply Real.sqrt_le_sqrt
  rw [cellGradeRow_norm_sq]
  unfold diskSupEnergy
  rw [Finset.mul_sum]
  set rowTerm : GradeMultiIndex (grade + 2) → ℝ := fun index =>
    cellFrequency cell ^ (2 * (grade + 2 - cartesianOrder index.toCartesian)) *
      ‖closedContinuousToDiskL2 (closedMultiDerivative
        (phaseWeightedJet parameters cell field) index.toCartesian)‖ ^ 2 with rowTermDef
  have rowTermNonneg : ∀ index, 0 ≤ rowTerm index := by
    intro index
    rw [rowTermDef]
    exact mul_nonneg (pow_nonneg (cellFrequency_pos cell).le _) (sq_nonneg _)
  calc (∑ slot : Fin 6, (cellFrequency cell ^ grade) ^ 2 *
        ‖closedDerivativeL2 (diskSupMultiIndex slot)
          (phaseWeightedJet parameters cell field)‖ ^ 2) ≤
      ∑ slot : Fin 6, rowTerm (liftedSupIndex grade slot) := by
        apply Finset.sum_le_sum
        intro slot _
        rw [rowTermDef]
        have orderLe := diskSupMultiIndex_order_le_two slot
        have powerLe : (cellFrequency cell ^ grade) ^ 2 ≤
            cellFrequency cell ^ (2 * (grade + 2 - cartesianOrder
              ((liftedSupIndex grade slot).toCartesian))) := by
          rw [← pow_mul, liftedSupIndex_toCartesian]
          apply pow_le_pow_right₀ (cellFrequency_one_le cell)
          omega
        apply mul_le_mul_of_nonneg_right powerLe
        exact sq_nonneg _
      _ = ∑ index ∈ Finset.univ.image (liftedSupIndex grade), rowTerm index :=
        (Finset.sum_image (fun first _ second _ equal =>
          liftedSupIndex_injective grade equal)).symm
      _ ≤ ∑ index : GradeMultiIndex (grade + 2), rowTerm index := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro index _ _
        exact rowTermNonneg index

/-- The crude axis value trace: two grades against the weighted row. -/
theorem crude_value_trace {dimension : ℕ} (parameters : PhaseParameters)
    (field : ClosedJet dimension) (cell : ℤ) (grade : ℕ) :
    axisWeight parameters grade cell * ‖originValue field‖ ≤
      diskSupConstant *
        ‖cellGradeRowLinear (grade := grade + 2) parameters cell field‖ := by
  have valueIdentity : axisWeight parameters grade cell * ‖originValue field‖ =
      cellFrequency cell ^ grade *
        ‖originValue (phaseWeightedJet parameters cell field)‖ := by
    rw [phaseWeightedJet_originValue, norm_smul,
      Real.norm_of_nonneg (cartesianWeight_pos parameters cell _).le,
      axisWeight_eq_weight_origin]
    ring
  rw [valueIdentity]
  have supBound := diskSup_bound
    (phaseWeightedJet parameters cell field) originPoint
  calc cellFrequency cell ^ grade *
      ‖originValue (phaseWeightedJet parameters cell field)‖ ≤
      cellFrequency cell ^ grade * (diskSupConstant *
        Real.sqrt (diskSupEnergy
          (phaseWeightedJet parameters cell field))) := by
        apply mul_le_mul_of_nonneg_left supBound
          (pow_nonneg (cellFrequency_pos cell).le grade)
    _ = diskSupConstant * (cellFrequency cell ^ grade *
        Real.sqrt (diskSupEnergy
          (phaseWeightedJet parameters cell field))) := by ring
    _ ≤ diskSupConstant *
        ‖cellGradeRowLinear (grade := grade + 2) parameters cell field‖ :=
        mul_le_mul_of_nonneg_left (supEnergy_le_row parameters cell field grade)
          diskSupConstant_pos.le

/-- The shifted supremum indices for the gradient trace. -/
def liftedShiftIndex (grade : ℕ) (direction : Fin 2) (slot : Fin 6) :
    GradeMultiIndex (grade + 3) :=
  ⟨(⟨(diskSupMultiIndex slot).1 +
      (if direction = 0 then 1 else 0), by
      have componentLe := (diskSupIndex_component_le slot).1
      by_cases directionZero : direction = 0 <;> simp [directionZero] <;> omega⟩,
    ⟨(diskSupMultiIndex slot).2 +
      (if direction = 1 then 1 else 0), by
      have componentLe := (diskSupIndex_component_le slot).2
      by_cases directionOne : direction = 1 <;> simp [directionOne] <;> omega⟩), by
    have orderLe := diskSupMultiIndex_order_le_two slot
    change (diskSupMultiIndex slot).1 + (if direction = 0 then 1 else 0) +
      ((diskSupMultiIndex slot).2 + (if direction = 1 then 1 else 0)) ≤
        grade + 3
    unfold cartesianOrder at orderLe
    by_cases directionZero : direction = 0
    · rw [if_pos directionZero, if_neg (by rw [directionZero]; decide)]
      omega
    · have directionOne : direction = 1 := by omega
      rw [if_neg directionZero, if_pos directionOne]
      omega⟩

theorem liftedShiftIndex_injective (grade : ℕ) (direction : Fin 2) :
    Function.Injective (liftedShiftIndex grade direction) := by
  intro first second equal
  apply diskSupMultiIndex_injective
  have firstComponents : (diskSupMultiIndex first).1 + (if direction = 0 then 1 else 0) =
      (diskSupMultiIndex second).1 + (if direction = 0 then 1 else 0) :=
    congrArg (fun index : GradeMultiIndex (grade + 3) => index.val.1.val) equal
  have secondComponents : (diskSupMultiIndex first).2 + (if direction = 1 then 1 else 0) =
      (diskSupMultiIndex second).2 + (if direction = 1 then 1 else 0) :=
    congrArg (fun index : GradeMultiIndex (grade + 3) => index.val.2.val) equal
  exact Prod.ext (Nat.add_right_cancel firstComponents)
    (Nat.add_right_cancel secondComponents)

/-- The single-letter derivative shift acts on the canonical indices by the
exact component increment. -/
theorem shiftedCartesianIndex_single (direction : Fin 2) (index : CartesianMultiIndex) :
    shiftedCartesianIndex (fun _ : Fin 1 => direction) index =
      (index.1 + (if direction = 0 then 1 else 0),
        index.2 + (if direction = 1 then 1 else 0)) := by
  unfold shiftedCartesianIndex cartesianWordIndex
  rw [List.ofFn_fin_append,
    show List.ofFn (fun _ : Fin 1 => direction) = [direction] from rfl,
    list_ofFn_cartesianMultiIndexWord]
  fin_cases direction
  · rw [show ((⟨0, by omega⟩ : Fin 2) = (0 : Fin 2)) from rfl]
    rw [if_pos rfl, if_neg (by decide : ¬(0 : Fin 2) = 1)]
    apply Prod.ext <;>
      simp [List.count_append, List.count_replicate]
  · rw [show ((⟨1, by omega⟩ : Fin 2) = (1 : Fin 2)) from rfl]
    rw [if_neg (by decide : ¬(1 : Fin 2) = 0), if_pos rfl]
    apply Prod.ext <;>
      simp [List.count_append, List.count_replicate]

theorem liftedShiftIndex_toCartesian (grade : ℕ) (direction : Fin 2) (slot : Fin 6) :
    (liftedShiftIndex grade direction slot).toCartesian =
      shiftedCartesianIndex (fun _ : Fin 1 => direction)
        (diskSupMultiIndex slot) := by
  rw [shiftedCartesianIndex_single]
  rfl

/-- The shifted supremum energy of a weighted jet against the grade row. -/
theorem shiftEnergy_le_row {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) (grade : ℕ) (direction : Fin 2) :
    cellFrequency cell ^ grade *
        Real.sqrt (diskSupEnergy
          (partialJet direction (phaseWeightedJet parameters cell field))) ≤
      ‖cellGradeRowLinear (grade := grade + 3) parameters cell field‖ := by
  have powNonneg : (0 : ℝ) ≤ cellFrequency cell ^ grade :=
    pow_nonneg (cellFrequency_pos cell).le grade
  rw [show cellFrequency cell ^ grade *
      Real.sqrt (diskSupEnergy
        (partialJet direction (phaseWeightedJet parameters cell field))) =
      Real.sqrt ((cellFrequency cell ^ grade) ^ 2 *
        diskSupEnergy
          (partialJet direction (phaseWeightedJet parameters cell field))) from by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq powNonneg]]
  rw [show ‖cellGradeRowLinear (grade := grade + 3) parameters cell field‖ =
      Real.sqrt (‖cellGradeRowLinear (grade := grade + 3) parameters cell field‖ ^ 2) from
    (Real.sqrt_sq (norm_nonneg _)).symm]
  apply Real.sqrt_le_sqrt
  rw [cellGradeRow_norm_sq]
  unfold diskSupEnergy
  rw [Finset.mul_sum]
  set rowTerm : GradeMultiIndex (grade + 3) → ℝ := fun index =>
    cellFrequency cell ^ (2 * (grade + 3 - cartesianOrder index.toCartesian)) *
      ‖closedContinuousToDiskL2 (closedMultiDerivative
        (phaseWeightedJet parameters cell field) index.toCartesian)‖ ^ 2 with rowTermDef
  have rowTermNonneg : ∀ index, 0 ≤ rowTerm index := by
    intro index
    rw [rowTermDef]
    exact mul_nonneg (pow_nonneg (cellFrequency_pos cell).le _) (sq_nonneg _)
  calc (∑ slot : Fin 6, (cellFrequency cell ^ grade) ^ 2 *
        ‖closedDerivativeL2 (diskSupMultiIndex slot)
          (partialJet direction (phaseWeightedJet parameters cell field))‖ ^ 2) ≤
      ∑ slot : Fin 6, rowTerm (liftedShiftIndex grade direction slot) := by
        apply Finset.sum_le_sum
        intro slot _
        rw [rowTermDef]
        have derivativeIdentity : closedDerivativeL2
            (diskSupMultiIndex slot)
            (partialJet direction (phaseWeightedJet parameters cell field)) =
            closedContinuousToDiskL2 (closedMultiDerivative
              (phaseWeightedJet parameters cell field)
              ((liftedShiftIndex grade direction slot).toCartesian)) := by
          change closedContinuousToDiskL2 (closedMultiDerivative
            (partialJet direction (phaseWeightedJet parameters cell field))
            (diskSupMultiIndex slot)) = _
          rw [liftedShiftIndex_toCartesian]
          congr 1
          exact shiftedClosedJet_closedMultiDerivative
            (phaseWeightedJet parameters cell field) (fun _ : Fin 1 => direction)
            (diskSupMultiIndex slot)
        rw [derivativeIdentity]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        rw [← pow_mul]
        apply pow_le_pow_right₀ (cellFrequency_one_le cell)
        have orderLe := diskSupMultiIndex_order_le_two slot
        have orderIdentity : cartesianOrder
            ((liftedShiftIndex grade direction slot).toCartesian) =
            cartesianOrder (diskSupMultiIndex slot) + 1 := by
          rw [liftedShiftIndex_toCartesian, shiftedCartesianIndex_order]
        omega
      _ = ∑ index ∈ Finset.univ.image (liftedShiftIndex grade direction), rowTerm index :=
        (Finset.sum_image (fun first _ second _ equal =>
          liftedShiftIndex_injective grade direction equal)).symm
      _ ≤ ∑ index : GradeMultiIndex (grade + 3), rowTerm index := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro index _ _
        exact rowTermNonneg index

/-- The crude axis gradient trace: three grades against the weighted row. -/
theorem crude_gradient_trace {dimension : ℕ} (parameters : PhaseParameters)
    (field : ClosedJet dimension) (cell : ℤ) (grade : ℕ) (direction : Fin 2) :
    axisWeight parameters grade cell * ‖originPartial direction field‖ ≤
      diskSupConstant *
        ‖cellGradeRowLinear (grade := grade + 3) parameters cell field‖ := by
  have valueIdentity : axisWeight parameters grade cell *
      ‖originPartial direction field‖ =
      cellFrequency cell ^ grade *
        ‖originPartial direction (phaseWeightedJet parameters cell field)‖ := by
    rw [phaseWeightedJet_originPartial, norm_smul,
      Real.norm_of_nonneg (cartesianWeight_pos parameters cell _).le,
      axisWeight_eq_weight_origin]
    ring
  rw [valueIdentity]
  have supBound := diskSup_bound
    (partialJet direction (phaseWeightedJet parameters cell field)) originPoint
  calc cellFrequency cell ^ grade *
      ‖originPartial direction (phaseWeightedJet parameters cell field)‖ ≤
      cellFrequency cell ^ grade * (diskSupConstant *
        Real.sqrt (diskSupEnergy
          (partialJet direction (phaseWeightedJet parameters cell field)))) := by
        apply mul_le_mul_of_nonneg_left supBound
          (pow_nonneg (cellFrequency_pos cell).le grade)
    _ = diskSupConstant * (cellFrequency cell ^ grade *
        Real.sqrt (diskSupEnergy
          (partialJet direction (phaseWeightedJet parameters cell field)))) := by ring
    _ ≤ diskSupConstant *
        ‖cellGradeRowLinear (grade := grade + 3) parameters cell field‖ :=
        mul_le_mul_of_nonneg_left (shiftEnergy_le_row parameters cell field grade direction)
          diskSupConstant_pos.le

end Grad.AxisSplit
