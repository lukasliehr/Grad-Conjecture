import AxisDerivativeRows

noncomputable section

open scoped BigOperators

namespace Grad.AxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds

variable {parameters : PhaseParameters}

/-! ### Elementary coefficient-core value plumbing -/

theorem acore_val_add {dimension : ℕ} (first second : ACore parameters dimension)
    (cell : ℤ) : ((first + second).val cell) = first.val cell + second.val cell := rfl

theorem acore_val_sub {dimension : ℕ} (first second : ACore parameters dimension)
    (cell : ℤ) : ((first - second).val cell) = first.val cell - second.val cell := rfl

theorem acore_val_neg {dimension : ℕ} (field : ACore parameters dimension)
    (cell : ℤ) : ((-field).val cell) = -(field.val cell) := rfl

theorem acore_val_smul {dimension : ℕ} (scalar : ℂ) (field : ACore parameters dimension)
    (cell : ℤ) : ((scalar • field).val cell) = scalar • field.val cell := rfl

theorem acore_val_zero {dimension : ℕ} (cell : ℤ) :
    ((0 : ACore parameters dimension).val cell) = 0 := rfl

/-! ### The degree parts evaluated on one argument tuple, row by row -/

theorem degreeOne_row_zero (cellLength : ℝ) (direction : QuotientState parameters) :
    (quotientDegreeOnePart parameters cellLength ![direction]) 0 =
      partialPlusCore parameters (statePotential direction) := by
  simp only [quotientDegreeOnePart, add_apply, rowInsert_apply,
    stateLinearMultilinear_apply, Pi.add_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.sub_apply]
  rw [Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 1),
    Pi.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 3)]
  rw [add_zero, add_zero]
  rfl

theorem degreeOne_row_one (cellLength : ℝ) (direction : QuotientState parameters) :
    (quotientDegreeOnePart parameters cellLength ![direction]) 1 =
      partialMinusCore parameters (statePotential direction) := by
  simp only [quotientDegreeOnePart, add_apply, rowInsert_apply,
    stateLinearMultilinear_apply, Pi.add_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.sub_apply]
  rw [Pi.single_eq_of_ne (by decide : (1 : Fin 4) ≠ 0), Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide : (1 : Fin 4) ≠ 3)]
  rw [zero_add, add_zero]
  rfl

theorem degreeOne_row_three (cellLength : ℝ) (direction : QuotientState parameters) :
    (quotientDegreeOnePart parameters cellLength ![direction]) 3 =
      removeAngularCore parameters (dotOperation parameters
        (rotationCore parameters (stateField direction))
        ((cellLength : ℂ) • eTConstantCore parameters)) -
      removeAngularCore parameters
        (timeDerivativeCore parameters (statePotential direction)) := by
  simp only [quotientDegreeOnePart, add_apply, rowInsert_apply,
    stateLinearMultilinear_apply, Pi.add_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.sub_apply]
  rw [Pi.single_eq_of_ne (by decide : (3 : Fin 4) ≠ 0),
    Pi.single_eq_of_ne (by decide : (3 : Fin 4) ≠ 1), Pi.single_eq_same]
  rw [zero_add, zero_add]
  rfl

theorem degreeTwo_row_zero (cellLength : ℝ)
    (arguments : Fin 2 → QuotientState parameters) :
    (quotientDegreeTwoPart parameters cellLength arguments) 0 =
      -(dotOperation parameters
          (partialPlusCore parameters (stateField (arguments 0)))
          (rotationCore parameters (stateField (arguments 1)))) +
        zMulCore parameters (quotientDotCurried parameters
          (stateField (arguments 0)) (stateField (arguments 1))) := by
  simp only [quotientDegreeTwoPart, add_apply, neg_apply,
    rowInsert_apply, stateBilinearMultilinear_apply, Pi.add_apply, LinearMap.coe_comp,
    Function.comp_apply]
  rw [Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 1),
    Pi.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 2),
    Pi.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 3)]
  rw [add_zero, add_zero, add_zero]
  rfl

theorem degreeTwo_row_one (cellLength : ℝ)
    (arguments : Fin 2 → QuotientState parameters) :
    (quotientDegreeTwoPart parameters cellLength arguments) 1 =
      -(dotOperation parameters
          (partialMinusCore parameters (stateField (arguments 0)))
          (rotationCore parameters (stateField (arguments 1)))) +
        starZMulCore parameters (quotientDotCurried parameters
          (stateField (arguments 0)) (stateField (arguments 1))) := by
  simp only [quotientDegreeTwoPart, add_apply, neg_apply,
    rowInsert_apply, stateBilinearMultilinear_apply, Pi.add_apply, LinearMap.coe_comp,
    Function.comp_apply]
  rw [Pi.single_eq_of_ne (by decide : (1 : Fin 4) ≠ 0), Pi.single_eq_same,
    Pi.single_eq_of_ne (by decide : (1 : Fin 4) ≠ 2),
    Pi.single_eq_of_ne (by decide : (1 : Fin 4) ≠ 3)]
  rw [zero_add, add_zero, add_zero]
  rfl

theorem degreeTwo_row_three (cellLength : ℝ)
    (arguments : Fin 2 → QuotientState parameters) :
    (quotientDegreeTwoPart parameters cellLength arguments) 3 =
      removeAngularCore parameters (dotOperation parameters
        (rotationCore parameters (stateField (arguments 0)))
        (timeDerivativeCore parameters (stateField (arguments 1)))) := by
  simp only [quotientDegreeTwoPart, add_apply, neg_apply,
    rowInsert_apply, stateBilinearMultilinear_apply, Pi.add_apply, LinearMap.coe_comp,
    Function.comp_apply]
  rw [Pi.single_eq_of_ne (by decide : (3 : Fin 4) ≠ 0),
    Pi.single_eq_of_ne (by decide : (3 : Fin 4) ≠ 1),
    Pi.single_eq_of_ne (by decide : (3 : Fin 4) ≠ 2), Pi.single_eq_same]
  rw [zero_add, zero_add, zero_add]
  rfl

theorem degreeThree_row_zero (arguments : Fin 3 → QuotientState parameters) :
    (quotientDegreeThreePart parameters arguments) 0 = 0 := by
  simp only [quotientDegreeThreePart, add_apply, rowInsert_apply,
    Pi.add_apply]
  rw [Pi.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 2),
    Pi.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 3), add_zero]

theorem degreeThree_row_one (arguments : Fin 3 → QuotientState parameters) :
    (quotientDegreeThreePart parameters arguments) 1 = 0 := by
  simp only [quotientDegreeThreePart, add_apply, rowInsert_apply,
    Pi.add_apply]
  rw [Pi.single_eq_of_ne (by decide : (1 : Fin 4) ≠ 2),
    Pi.single_eq_of_ne (by decide : (1 : Fin 4) ≠ 3), add_zero]

theorem degreeThree_row_three (arguments : Fin 3 → QuotientState parameters) :
    (quotientDegreeThreePart parameters arguments) 3 =
      stateScalar (arguments 0) • removeAngularCore parameters (dotOperation parameters
        (rotationCore parameters (stateField (arguments 1)))
        (valueMapCore parameters tangentGeneratorMap (stateField (arguments 2)))) := by
  simp only [quotientDegreeThreePart, add_apply, rowInsert_apply,
    stateScalarWrap_apply, stateBilinearMultilinear_apply, stateTrilinearMultilinear_apply,
    Pi.add_apply, LinearMap.coe_comp, Function.comp_apply]
  rw [Pi.single_eq_of_ne (by decide : (3 : Fin 4) ≠ 2), Pi.single_eq_same, zero_add]
  rfl

theorem degreeFour_row_zero (arguments : Fin 4 → QuotientState parameters) :
    (quotientDegreeFourPart parameters arguments) 0 = 0 := by
  simp only [quotientDegreeFourPart, rowInsert_apply]
  rw [Pi.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 2)]

theorem degreeFour_row_one (arguments : Fin 4 → QuotientState parameters) :
    (quotientDegreeFourPart parameters arguments) 1 = 0 := by
  simp only [quotientDegreeFourPart, rowInsert_apply]
  rw [Pi.single_eq_of_ne (by decide : (1 : Fin 4) ≠ 2)]

theorem degreeFour_row_three (arguments : Fin 4 → QuotientState parameters) :
    (quotientDegreeFourPart parameters arguments) 3 = 0 := by
  simp only [quotientDegreeFourPart, rowInsert_apply]
  rw [Pi.single_eq_of_ne (by decide : (3 : Fin 4) ≠ 2)]

/-! ### Origin traces of the assembled terms -/

/-- The mean-free wrapper is invisible to the axis first derivative. -/
theorem removeAngular_originPartial (direction : Fin 2)
    (field : ACore parameters 1) (cell : ℤ) :
    originPartial direction ((removeAngularCore parameters field).val cell) =
      originPartial direction (field.val cell) := by
  have expand : (removeAngularCore parameters field).val cell =
      field.val cell - angularClosedJet 0 (field.val cell) := rfl
  rw [expand, originPartial_sub, angularJet_zero_originPartial, sub_zero]

theorem rotationCore_apply {dimension : ℕ} (field : ACore parameters dimension) :
    rotationCore parameters field =
      coordinateCore parameters 0 (partialCore parameters 1 field) -
        coordinateCore parameters 1 (partialCore parameters 0 field) := rfl

theorem dotOperation_originValue_zero_right (first second : ACore parameters 3)
    (secondVanishes : ∀ cell : ℤ, originValue (second.val cell) = 0) (cell : ℤ) :
    originValue ((dotOperation parameters first second).val cell) = 0 :=
  pairProduct_originValue_zero_right physicalDotProduct first second secondVanishes cell

theorem dotOperation_originValue_constant_right (first : ACore parameters 3)
    (vector : ComplexEuclidean 3) (cell : ℤ) :
    originValue ((dotOperation parameters first
        (constantCore parameters vector)).val cell) =
      physicalDotProduct ![originValue (first.val cell), vector] :=
  pairProduct_originValue_constant_right physicalDotProduct first vector cell

theorem dotOperation_coordinate_left (coordinate : Fin 2)
    (first second : ACore parameters 3) :
    dotOperation parameters (coordinateCore parameters coordinate first) second =
      coordinateCore parameters coordinate (dotOperation parameters first second) :=
  pairProduct_coordinate_left physicalDotProduct coordinate first second

/-- Axis first derivative of `dot(R a, c)`, reduced by the coordinate
pull-out to axis values. -/
theorem dotRotation_originPartial {direction : Fin 2}
    (first second : ACore parameters 3) (cell : ℤ) :
    originPartial direction ((dotOperation parameters
        (rotationCore parameters first) second).val cell) =
      (if direction = 0 then
        originValue ((dotOperation parameters
          (partialCore parameters 1 first) second).val cell) else 0) -
      (if direction = 1 then
        originValue ((dotOperation parameters
          (partialCore parameters 0 first) second).val cell) else 0) := by
  rw [rotationCore_apply]
  have splitDot : dotOperation parameters
      (coordinateCore parameters 0 (partialCore parameters 1 first) -
        coordinateCore parameters 1 (partialCore parameters 0 first)) second =
      dotOperation parameters
        (coordinateCore parameters 0 (partialCore parameters 1 first)) second -
      dotOperation parameters
        (coordinateCore parameters 1 (partialCore parameters 0 first)) second := by
    rw [map_sub]
    rfl
  rw [splitDot]
  have pullZero : dotOperation parameters
      (coordinateCore parameters 0 (partialCore parameters 1 first)) second =
      coordinateCore parameters 0 (dotOperation parameters
        (partialCore parameters 1 first) second) :=
    pairProduct_coordinate_left physicalDotProduct 0 (partialCore parameters 1 first) second
  have pullOne : dotOperation parameters
      (coordinateCore parameters 1 (partialCore parameters 0 first)) second =
      coordinateCore parameters 1 (dotOperation parameters
        (partialCore parameters 0 first) second) :=
    pairProduct_coordinate_left physicalDotProduct 1 (partialCore parameters 0 first) second
  rw [pullZero, pullOne, acore_val_sub, originPartial_sub, coordinateCore_val,
    coordinateCore_val, coordinateJet_originPartial, coordinateJet_originPartial]

/-- Axis first derivative of `dot(R a, c)` vanishes when every cell of `c`
has zero axis value. -/
theorem dotRotation_originPartial_zero {direction : Fin 2}
    (first second : ACore parameters 3)
    (secondVanishes : ∀ cell : ℤ, originValue (second.val cell) = 0) (cell : ℤ) :
    originPartial direction ((dotOperation parameters
        (rotationCore parameters first) second).val cell) = 0 := by
  rw [dotRotation_originPartial]
  rw [dotOperation_originValue_zero_right _ second secondVanishes,
    dotOperation_originValue_zero_right _ second secondVanishes]
  simp only [ite_self, sub_zero]

theorem timeDerivative_originValue_vanish {dimension : ℕ}
    (field : ACore parameters dimension)
    (fieldVanishes : ∀ cell : ℤ, originValue (field.val cell) = 0) (cell : ℤ) :
    originValue ((timeDerivativeCore parameters field).val cell) = 0 := by
  rw [timeDerivativeCore_val, originValue_smul, fieldVanishes, smul_zero]

theorem valueMap_originValue_vanish {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : ACore parameters sourceDimension)
    (fieldVanishes : ∀ cell : ℤ, originValue (field.val cell) = 0) (cell : ℤ) :
    originValue ((valueMapCore parameters mapping field).val cell) = 0 := by
  rw [valueMapCore_originValue, fieldVanishes, map_zero]

/-! ### The three traced rows of the first derivative -/

/-- Row zero of the linearization has axis value `∂₊S(0)`, at every state. -/
theorem derivativeRows_row_zero_originValue (cellLength : ℝ)
    (base direction : QuotientState parameters) (cell : ℤ) :
    originValue (((quotientRowsDerivative parameters cellLength 1 base ![direction]) 0).val
        cell) =
      originValue ((partialPlusCore parameters (statePotential direction)).val cell) := by
  have expand := functional_rowsDerivative_one
    (rowsOriginValue (parameters := parameters) 0 cell) cellLength base direction
  rw [rowsOriginValue_apply] at expand
  rw [expand]
  have degreeTwoVanish : ∀ slot : Fin 2,
      rowsOriginValue (parameters := parameters) 0 cell (quotientDegreeTwoPart parameters
        cellLength (Function.update (fun _ => base) slot direction)) = 0 := by
    intro slot
    rw [rowsOriginValue_apply, degreeTwo_row_zero, acore_val_add, originValue_add,
      acore_val_neg, originValue_neg,
      dotOperation_originValue_zero_right _ _ (rotationCore_originValue _) cell,
      zMulCore_originValue, neg_zero, add_zero]
  have degreeThreeVanish : ∀ slot : Fin 3,
      rowsOriginValue (parameters := parameters) 0 cell (quotientDegreeThreePart parameters
        (Function.update (fun _ => base) slot direction)) = 0 := by
    intro slot
    rw [rowsOriginValue_apply, degreeThree_row_zero, acore_val_zero, originValue_zero]
  have degreeFourVanish : ∀ slot : Fin 4,
      rowsOriginValue (parameters := parameters) 0 cell (quotientDegreeFourPart parameters
        (Function.update (fun _ => base) slot direction)) = 0 := by
    intro slot
    rw [rowsOriginValue_apply, degreeFour_row_zero, acore_val_zero, originValue_zero]
  rw [Finset.sum_congr rfl (fun slot _ => degreeTwoVanish slot),
    Finset.sum_congr rfl (fun slot _ => degreeThreeVanish slot),
    Finset.sum_congr rfl (fun slot _ => degreeFourVanish slot),
    Finset.sum_const_zero, Finset.sum_const_zero, Finset.sum_const_zero,
    add_zero, add_zero, add_zero]
  rw [rowsOriginValue_apply, degreeOne_row_zero]

/-- Row one of the linearization has axis value `∂₋S(0)`, at every state. -/
theorem derivativeRows_row_one_originValue (cellLength : ℝ)
    (base direction : QuotientState parameters) (cell : ℤ) :
    originValue (((quotientRowsDerivative parameters cellLength 1 base ![direction]) 1).val
        cell) =
      originValue ((partialMinusCore parameters (statePotential direction)).val cell) := by
  have expand := functional_rowsDerivative_one
    (rowsOriginValue (parameters := parameters) 1 cell) cellLength base direction
  rw [rowsOriginValue_apply] at expand
  rw [expand]
  have degreeTwoVanish : ∀ slot : Fin 2,
      rowsOriginValue (parameters := parameters) 1 cell (quotientDegreeTwoPart parameters
        cellLength (Function.update (fun _ => base) slot direction)) = 0 := by
    intro slot
    rw [rowsOriginValue_apply, degreeTwo_row_one, acore_val_add, originValue_add,
      acore_val_neg, originValue_neg,
      dotOperation_originValue_zero_right _ _ (rotationCore_originValue _) cell,
      starZMulCore_originValue, neg_zero, add_zero]
  have degreeThreeVanish : ∀ slot : Fin 3,
      rowsOriginValue (parameters := parameters) 1 cell (quotientDegreeThreePart parameters
        (Function.update (fun _ => base) slot direction)) = 0 := by
    intro slot
    rw [rowsOriginValue_apply, degreeThree_row_one, acore_val_zero, originValue_zero]
  have degreeFourVanish : ∀ slot : Fin 4,
      rowsOriginValue (parameters := parameters) 1 cell (quotientDegreeFourPart parameters
        (Function.update (fun _ => base) slot direction)) = 0 := by
    intro slot
    rw [rowsOriginValue_apply, degreeFour_row_one, acore_val_zero, originValue_zero]
  rw [Finset.sum_congr rfl (fun slot _ => degreeTwoVanish slot),
    Finset.sum_congr rfl (fun slot _ => degreeThreeVanish slot),
    Finset.sum_congr rfl (fun slot _ => degreeFourVanish slot),
    Finset.sum_const_zero, Finset.sum_const_zero, Finset.sum_const_zero,
    add_zero, add_zero, add_zero]
  rw [rowsOriginValue_apply, degreeOne_row_one]

/-- Row three of the linearization: at an axis-vanishing state and an
axis-vanishing direction, only the affine `L e_T` pairing and the scalar
cell derivative survive at the axis. -/
theorem derivativeRows_row_three_originPartial (cellLength : ℝ)
    (base direction : QuotientState parameters)
    (baseVanishes : ∀ cell : ℤ, originValue ((stateField base).val cell) = 0)
    (directionVanishes : ∀ cell : ℤ, originValue ((stateField direction).val cell) = 0)
    (partialDirection : Fin 2) (cell : ℤ) :
    originPartial partialDirection
        (((quotientRowsDerivative parameters cellLength 1 base ![direction]) 3).val cell) =
      (cellLength : ℂ) •
        ((if partialDirection = 0 then
          originValue ((dotOperation parameters
            (partialCore parameters 1 (stateField direction))
            (eTConstantCore parameters)).val cell) else 0) -
        (if partialDirection = 1 then
          originValue ((dotOperation parameters
            (partialCore parameters 0 (stateField direction))
            (eTConstantCore parameters)).val cell) else 0)) -
      ((cell : ℂ) * Complex.I) •
        originPartial partialDirection ((statePotential direction).val cell) := by
  have stateUpdateVanishes : ∀ {slots : ℕ} (slot other : Fin slots), ∀ cellIndex : ℤ,
      originValue ((stateField (Function.update
        (fun _ : Fin slots => base) slot direction other)).val cellIndex) = 0 := by
    intro slots slot other cellIndex
    by_cases hit : other = slot
    · rw [hit, Function.update_self]
      exact directionVanishes cellIndex
    · rw [Function.update_of_ne hit]
      exact baseVanishes cellIndex
  have expand := functional_rowsDerivative_one
    (rowsOriginPartial (parameters := parameters) partialDirection 3 cell)
    cellLength base direction
  rw [rowsOriginPartial_apply] at expand
  rw [expand]
  have degreeTwoVanish : ∀ slot : Fin 2,
      rowsOriginPartial (parameters := parameters) partialDirection 3 cell
        (quotientDegreeTwoPart parameters cellLength
          (Function.update (fun _ => base) slot direction)) = 0 := by
    intro slot
    rw [rowsOriginPartial_apply, degreeTwo_row_three, removeAngular_originPartial]
    exact dotRotation_originPartial_zero _ _
      (fun cellIndex => timeDerivative_originValue_vanish _
        (stateUpdateVanishes slot 1) cellIndex) cell
  have degreeThreeVanish : ∀ slot : Fin 3,
      rowsOriginPartial (parameters := parameters) partialDirection 3 cell
        (quotientDegreeThreePart parameters
          (Function.update (fun _ => base) slot direction)) = 0 := by
    intro slot
    rw [rowsOriginPartial_apply, degreeThree_row_three, acore_val_smul, originPartial_smul,
      removeAngular_originPartial]
    rw [dotRotation_originPartial_zero _ _
      (fun cellIndex => valueMap_originValue_vanish tangentGeneratorMap _
        (stateUpdateVanishes slot 2) cellIndex) cell, smul_zero]
  have degreeFourVanish : ∀ slot : Fin 4,
      rowsOriginPartial (parameters := parameters) partialDirection 3 cell
        (quotientDegreeFourPart parameters
          (Function.update (fun _ => base) slot direction)) = 0 := by
    intro slot
    rw [rowsOriginPartial_apply, degreeFour_row_three, acore_val_zero, originPartial_zero]
  rw [Finset.sum_congr rfl (fun slot _ => degreeTwoVanish slot),
    Finset.sum_congr rfl (fun slot _ => degreeThreeVanish slot),
    Finset.sum_congr rfl (fun slot _ => degreeFourVanish slot),
    Finset.sum_const_zero, Finset.sum_const_zero, Finset.sum_const_zero,
    add_zero, add_zero, add_zero]
  rw [rowsOriginPartial_apply, degreeOne_row_three]
  rw [acore_val_sub, originPartial_sub, removeAngular_originPartial,
    removeAngular_originPartial]
  have smulSecond : dotOperation parameters
      (rotationCore parameters (stateField direction))
      ((cellLength : ℂ) • eTConstantCore parameters) =
      (cellLength : ℂ) • dotOperation parameters
        (rotationCore parameters (stateField direction)) (eTConstantCore parameters) := by
    rw [map_smul]
  rw [smulSecond, acore_val_smul, originPartial_smul, dotRotation_originPartial]
  rw [timeDerivativeCore_val, originPartial_smul]

end Grad.AxisSplit
