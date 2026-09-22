import AxisAngularOrigin

noncomputable section

open scoped BigOperators

namespace Grad.AxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds

variable {parameters : PhaseParameters}

/-- The rotation core is the literal coordinate/partial combination, cell by cell. -/
theorem rotationCore_val {dimension : ℕ} (field : ACore parameters dimension) (cell : ℤ) :
    (rotationCore parameters field).val cell =
      coordinateJet 0 (partialJet 1 (field.val cell)) -
        coordinateJet 1 (partialJet 0 (field.val cell)) := rfl

theorem coordinateCore_val {dimension : ℕ} (coordinate : Fin 2)
    (field : ACore parameters dimension) (cell : ℤ) :
    (coordinateCore parameters coordinate field).val cell =
      coordinateJet coordinate (field.val cell) := rfl

theorem partialCore_val {dimension : ℕ} (direction : Fin 2)
    (field : ACore parameters dimension) (cell : ℤ) :
    (partialCore parameters direction field).val cell =
      partialJet direction (field.val cell) := rfl

theorem timeDerivativeCore_val {dimension : ℕ} (field : ACore parameters dimension)
    (cell : ℤ) :
    (timeDerivativeCore parameters field).val cell =
      ((cell : ℂ) * Complex.I) • field.val cell := rfl

/-- Rotation kills every axis value, for every field. -/
theorem rotationCore_originValue {dimension : ℕ} (field : ACore parameters dimension)
    (cell : ℤ) :
    originValue ((rotationCore parameters field).val cell) = 0 := by
  rw [rotationCore_val, originValue_sub, coordinateJet_originValue,
    coordinateJet_originValue, sub_zero]

/-- The exact axis first derivatives of the rotation: `D(Rf)(0) = Df(0) J`. -/
theorem rotationCore_originPartial_zero {dimension : ℕ}
    (field : ACore parameters dimension) (cell : ℤ) :
    originPartial 0 ((rotationCore parameters field).val cell) =
      originPartial 1 (field.val cell) := by
  rw [rotationCore_val, originPartial_sub, coordinateJet_originPartial,
    coordinateJet_originPartial]
  rw [if_pos rfl, if_neg (by decide : ¬(0 : Fin 2) = 1), sub_zero]
  rfl

theorem rotationCore_originPartial_one {dimension : ℕ}
    (field : ACore parameters dimension) (cell : ℤ) :
    originPartial 1 ((rotationCore parameters field).val cell) =
      -originPartial 0 (field.val cell) := by
  rw [rotationCore_val, originPartial_sub, coordinateJet_originPartial,
    coordinateJet_originPartial]
  rw [if_neg (by decide : ¬(1 : Fin 2) = 0), if_pos rfl, zero_sub]
  rfl

/-- Multiplication by `z` or `z̄` kills every axis value. -/
theorem zMulCore_originValue {dimension : ℕ} (field : ACore parameters dimension)
    (cell : ℤ) :
    originValue ((zMulCore parameters field).val cell) = 0 := by
  have expand : (zMulCore parameters field).val cell =
      coordinateJet 0 (field.val cell) +
        Complex.I • coordinateJet 1 (field.val cell) := rfl
  rw [expand, originValue_add, originValue_smul, coordinateJet_originValue,
    coordinateJet_originValue, smul_zero, add_zero]

theorem starZMulCore_originValue {dimension : ℕ} (field : ACore parameters dimension)
    (cell : ℤ) :
    originValue ((starZMulCore parameters field).val cell) = 0 := by
  have expand : (starZMulCore parameters field).val cell =
      coordinateJet 0 (field.val cell) -
        Complex.I • coordinateJet 1 (field.val cell) := rfl
  rw [expand, originValue_sub, originValue_smul, coordinateJet_originValue,
    coordinateJet_originValue, smul_zero, sub_zero]

theorem valueMapCore_originValue {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : ACore parameters sourceDimension) (cell : ℤ) :
    originValue ((valueMapCore parameters mapping field).val cell) =
      mapping (originValue (field.val cell)) := by
  rw [valueMapCore_val, valueMapJet_originValue]

/-- The pair-product value at the axis is the literal convolution of values. -/
theorem pairProduct_originValue {inputDimension outputDimension : ℕ}
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin 2 => ComplexEuclidean inputDimension)
      (ComplexEuclidean outputDimension))
    (first second : ACore parameters inputDimension) (cell : ℤ) :
    originValue ((pairProductLinear parameters multiplication first second).val cell) =
      productCoefficientValue multiplication ![first, second] cell originPoint := by
  rw [pairProductLinear_apply]
  exact actualMultilinearProduct_isActual parameters multiplication ![first, second]
    cell originPoint

/-- If every cell of the second factor vanishes at the axis, so does the
product value at the axis. -/
theorem pairProduct_originValue_zero_right {inputDimension outputDimension : ℕ}
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin 2 => ComplexEuclidean inputDimension)
      (ComplexEuclidean outputDimension))
    (first second : ACore parameters inputDimension)
    (secondVanishes : ∀ cell : ℤ, originValue (second.val cell) = 0) (cell : ℤ) :
    originValue ((pairProductLinear parameters multiplication first second).val cell) = 0 := by
  rw [pairProduct_originValue]
  unfold productCoefficientValue
  have termsVanish : ∀ cells : {indices : Fin 2 → ℤ // ∑ index, indices index = cell},
      multiplication (fun index =>
        ((![first, second] index).val (cells.val index)).value originPoint) = 0 := by
    intro cells
    apply multiplication.map_coord_zero (i := 1)
    exact secondVanishes (cells.val 1)
  rw [tsum_congr termsVanish, tsum_zero]

/-- The distinguished assignment placing the whole cell in the first slot. -/
def firstSlotAssignment (cell : ℤ) : {indices : Fin 2 → ℤ // ∑ index, indices index = cell} :=
  ⟨![cell, 0], by rw [Fin.sum_univ_two]; change cell + 0 = cell; rw [add_zero]⟩

/-- Convolution with a constant-cell field collapses to one term at the axis. -/
theorem pairProduct_originValue_constant_right {inputDimension outputDimension : ℕ}
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin 2 => ComplexEuclidean inputDimension)
      (ComplexEuclidean outputDimension))
    (first : ACore parameters inputDimension) (vector : ComplexEuclidean inputDimension)
    (cell : ℤ) :
    originValue ((pairProductLinear parameters multiplication first
        (constantCore parameters vector)).val cell) =
      multiplication ![originValue (first.val cell), vector] := by
  rw [pairProduct_originValue]
  unfold productCoefficientValue
  rw [tsum_eq_single (firstSlotAssignment cell) ?_]
  · congr 1
    funext index
    fin_cases index
    · change (first.val cell).value originPoint = originValue (first.val cell)
      rfl
    · change ((constantCore parameters vector).val 0).value originPoint = vector
      exact constantCore_value_zero vector originPoint
  · intro other otherNe
    have secondCell : other.val 1 ≠ 0 := by
      intro secondZero
      apply otherNe
      apply Subtype.ext
      funext index
      have sumProperty := other.property
      rw [Fin.sum_univ_two] at sumProperty
      fin_cases index
      · change other.val 0 = cell
        rw [secondZero, add_zero] at sumProperty
        exact sumProperty
      · exact secondZero
    apply multiplication.map_coord_zero (i := 1)
    change ((constantCore parameters vector).val (other.val 1)).value originPoint = 0
    exact constantCore_value_ne vector secondCell originPoint

/-- Coordinate multiplication moves through the first slot of the actual
pair product. -/
theorem pairProduct_coordinate_left {inputDimension outputDimension : ℕ}
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin 2 => ComplexEuclidean inputDimension)
      (ComplexEuclidean outputDimension))
    (coordinate : Fin 2) (first second : ACore parameters inputDimension) :
    pairProductLinear parameters multiplication
        (coordinateCore parameters coordinate first) second =
      coordinateCore parameters coordinate
        (pairProductLinear parameters multiplication first second) := by
  apply acore_ext
  intro cell point
  rw [pairProductLinear_apply, pairProductLinear_apply,
    actualMultilinearProduct_isActual parameters multiplication _ cell point]
  have rightSide : ((coordinateCore parameters coordinate
      (actualMultilinearProduct parameters multiplication ![first, second])).val cell).value
        point = point.val coordinate •
          productCoefficientValue multiplication ![first, second] cell point := by
    rw [coordinateCore_val, coordinateJet_value,
      actualMultilinearProduct_isActual parameters multiplication _ cell point]
  rw [rightSide]
  unfold productCoefficientValue
  rw [← tsum_const_smul'' (point.val coordinate)]
  apply tsum_congr
  intro cells
  have leftTerm : (fun index =>
      ((![coordinateCore parameters coordinate first, second] index).val
        (cells.val index)).value point) =
      Function.update (fun index =>
        ((![first, second] index).val (cells.val index)).value point) 0
        (point.val coordinate •
          ((first.val (cells.val 0)).value point)) := by
    funext index
    fin_cases index
    · change ((coordinateCore parameters coordinate first).val (cells.val 0)).value point = _
      rw [coordinateCore_val, coordinateJet_value]
      rfl
    · rfl
  rw [leftTerm]
  have realToComplex : point.val coordinate •
      ((first.val (cells.val 0)).value point) =
      ((point.val coordinate : ℝ) : ℂ) • ((first.val (cells.val 0)).value point) :=
    (Complex.coe_smul _ _).symm
  rw [realToComplex, multiplication.map_update_smul]
  have baseIdentity : Function.update (fun index =>
      ((![first, second] index).val (cells.val index)).value point) 0
        ((first.val (cells.val 0)).value point) = fun index =>
      ((![first, second] index).val (cells.val index)).value point := by
    funext index
    fin_cases index
    · rfl
    · rfl
  rw [baseIdentity]
  exact (Complex.coe_smul _ _).trans rfl

end Grad.AxisSplit
