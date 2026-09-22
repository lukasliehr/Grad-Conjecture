import QuotientStateSpace

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct

variable {parameters : PhaseParameters}

/-- Two original-core elements with the same actual coefficient values are equal. -/
theorem acore_ext {dimension : ℕ} {first second : ACore parameters dimension}
    (equalValues : ∀ cell point, (first.val cell).value point = (second.val cell).value point) :
    first = second := by
  apply Subtype.ext
  funext cell
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  exact equalValues cell point

theorem acore_add_value {dimension : ℕ} (first second : ACore parameters dimension)
    (cell : ℤ) (point : ClosedDisk) :
    ((first + second).val cell).value point =
      (first.val cell).value point + (second.val cell).value point := by
  change (first.val cell + second.val cell).value point = _
  rw [closedJet_value_add, ContinuousMap.add_apply]

theorem acore_smul_value {dimension : ℕ} (scalar : ℂ) (field : ACore parameters dimension)
    (cell : ℤ) (point : ClosedDisk) :
    ((scalar • field).val cell).value point = scalar • (field.val cell).value point := by
  change (scalar • field.val cell).value point = _
  rw [closedJet_value_smul, ContinuousMap.smul_apply]

/-- The actual convolution value series of any fixed multilinear physical
product is summable, cell by cell and point by point. -/
theorem productValue_summable {arity outputDimension inputDimension : ℕ}
    (positiveArity : 0 < arity)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin arity => ComplexEuclidean inputDimension) (ComplexEuclidean outputDimension))
    (fields : Fin arity → ACore parameters inputDimension) (cell : ℤ) (point : ClosedDisk) :
    Summable (fun assignment : CellAssignments arity cell =>
      multiplication (fun index => ((fields index).val (assignment.val index)).value point)) := by
  apply Summable.of_norm_bounded
    (((productSeriesMajorant_summable parameters multiplication fields 0).subtype _).mul_left
      ‖cartesianInverseWeight parameters cell point.val‖)
  intro assignment
  have derivBound := weightedProductAssignment_bound positiveArity parameters multiplication
    fields cell 0 assignment point.val point.property
  rw [norm_iteratedFDeriv_zero] at derivBound
  have valueForm := weightedProductSmooth_value parameters multiplication fields assignment.val point
  rw [assignment.property] at valueForm
  have unweight : multiplication
      (fun index => ((fields index).val (assignment.val index)).value point) =
      cartesianInverseWeight parameters cell point.val •
        weightedProductSmooth parameters assignment.val multiplication
          (fun index => (fields index).val (assignment.val index)) point.val := by
    rw [valueForm, smul_smul, mul_comm, cartesianWeight_mul_inverse, one_smul]
  rw [unweight, norm_smul]
  exact mul_le_mul_of_nonneg_left derivBound (norm_nonneg _)

theorem productValue_tuple_update {arity inputDimension : ℕ} [DecidableEq (Fin arity)]
    (fields : Fin arity → ACore parameters inputDimension) (slot : Fin arity)
    (replacement : ACore parameters inputDimension) (cells : Fin arity → ℤ) (point : ClosedDisk) :
    (fun index => (((Function.update fields slot replacement) index).val (cells index)).value point) =
      Function.update (fun index => ((fields index).val (cells index)).value point)
        slot ((replacement.val (cells slot)).value point) := by
  funext index
  exact Function.apply_update (fun index field => ((field.val (cells index)).value point))
    fields slot replacement index

theorem productCoefficientValue_update_add {arity outputDimension inputDimension : ℕ}
    [DecidableEq (Fin arity)] (positiveArity : 0 < arity)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin arity => ComplexEuclidean inputDimension) (ComplexEuclidean outputDimension))
    (fields : Fin arity → ACore parameters inputDimension) (slot : Fin arity)
    (first second : ACore parameters inputDimension) (cell : ℤ) (point : ClosedDisk) :
    productCoefficientValue multiplication (Function.update fields slot (first + second)) cell point =
      productCoefficientValue multiplication (Function.update fields slot first) cell point +
        productCoefficientValue multiplication (Function.update fields slot second) cell point := by
  unfold productCoefficientValue
  have splitTerm : ∀ assignment : CellAssignments arity cell,
      multiplication (fun index => (((Function.update fields slot (first + second)) index).val
        (assignment.val index)).value point) =
      multiplication (fun index => (((Function.update fields slot first) index).val
        (assignment.val index)).value point) +
      multiplication (fun index => (((Function.update fields slot second) index).val
        (assignment.val index)).value point) := by
    intro assignment
    rw [productValue_tuple_update fields slot (first + second) assignment.val point,
      productValue_tuple_update fields slot first assignment.val point,
      productValue_tuple_update fields slot second assignment.val point,
      acore_add_value]
    exact multiplication.map_update_add _ slot _ _
  rw [tsum_congr splitTerm]
  exact (productValue_summable positiveArity multiplication _ cell point).tsum_add
    (productValue_summable positiveArity multiplication _ cell point)

theorem productCoefficientValue_update_smul {arity outputDimension inputDimension : ℕ}
    [DecidableEq (Fin arity)]
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin arity => ComplexEuclidean inputDimension) (ComplexEuclidean outputDimension))
    (fields : Fin arity → ACore parameters inputDimension) (slot : Fin arity)
    (scalar : ℂ) (field : ACore parameters inputDimension) (cell : ℤ) (point : ClosedDisk) :
    productCoefficientValue multiplication (Function.update fields slot (scalar • field)) cell point =
      scalar • productCoefficientValue multiplication (Function.update fields slot field) cell point := by
  unfold productCoefficientValue
  have splitTerm : ∀ assignment : CellAssignments arity cell,
      multiplication (fun index => (((Function.update fields slot (scalar • field)) index).val
        (assignment.val index)).value point) =
      scalar • multiplication (fun index => (((Function.update fields slot field) index).val
        (assignment.val index)).value point) := by
    intro assignment
    rw [productValue_tuple_update fields slot (scalar • field) assignment.val point,
      productValue_tuple_update fields slot field assignment.val point,
      acore_smul_value]
    exact multiplication.map_update_smul _ slot _ _
  rw [tsum_congr splitTerm]
  exact tsum_const_smul'' scalar

/-- Slotwise additivity of the actual physical product construction. -/
theorem actualMultilinearProduct_update_add {arity outputDimension inputDimension : ℕ}
    [DecidableEq (Fin (arity + 1))]
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin (arity + 1) => ComplexEuclidean inputDimension) (ComplexEuclidean outputDimension))
    (fields : Fin (arity + 1) → ACore parameters inputDimension) (slot : Fin (arity + 1))
    (first second : ACore parameters inputDimension) :
    actualMultilinearProduct parameters multiplication (Function.update fields slot (first + second)) =
      actualMultilinearProduct parameters multiplication (Function.update fields slot first) +
        actualMultilinearProduct parameters multiplication (Function.update fields slot second) := by
  apply acore_ext
  intro cell point
  rw [acore_add_value,
    actualMultilinearProduct_isActual parameters multiplication _ cell point,
    actualMultilinearProduct_isActual parameters multiplication _ cell point,
    actualMultilinearProduct_isActual parameters multiplication _ cell point]
  exact productCoefficientValue_update_add (Nat.succ_pos arity) multiplication fields slot
    first second cell point

/-- Slotwise homogeneity of the actual physical product construction. -/
theorem actualMultilinearProduct_update_smul {arity outputDimension inputDimension : ℕ}
    [DecidableEq (Fin (arity + 1))]
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin (arity + 1) => ComplexEuclidean inputDimension) (ComplexEuclidean outputDimension))
    (fields : Fin (arity + 1) → ACore parameters inputDimension) (slot : Fin (arity + 1))
    (scalar : ℂ) (field : ACore parameters inputDimension) :
    actualMultilinearProduct parameters multiplication (Function.update fields slot (scalar • field)) =
      scalar • actualMultilinearProduct parameters multiplication (Function.update fields slot field) := by
  apply acore_ext
  intro cell point
  rw [acore_smul_value,
    actualMultilinearProduct_isActual parameters multiplication _ cell point,
    actualMultilinearProduct_isActual parameters multiplication _ cell point]
  exact productCoefficientValue_update_smul multiplication fields slot scalar field cell point

theorem pair_update_zero {Value : Type*} (first second replacement : Value) :
    Function.update ![first, second] (0 : Fin 2) replacement = ![replacement, second] := by
  funext index
  fin_cases index <;> simp

theorem pair_update_one {Value : Type*} (first second replacement : Value) :
    Function.update ![first, second] (1 : Fin 2) replacement = ![first, replacement] := by
  funext index
  fin_cases index <;> simp

theorem triple_update_zero {Value : Type*} (first second third replacement : Value) :
    Function.update ![first, second, third] (0 : Fin 3) replacement =
      ![replacement, second, third] := by
  funext index
  fin_cases index <;> simp

theorem triple_update_one {Value : Type*} (first second third replacement : Value) :
    Function.update ![first, second, third] (1 : Fin 3) replacement =
      ![first, replacement, third] := by
  funext index
  fin_cases index <;> simp

theorem triple_update_two {Value : Type*} (first second third replacement : Value) :
    Function.update ![first, second, third] (2 : Fin 3) replacement =
      ![first, second, replacement] := by
  funext index
  fin_cases index <;> simp

/-- The actual bilinear physical product, curried into complex-linear slots. -/
def pairProductLinear {outputDimension inputDimension : ℕ} (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin 2 => ComplexEuclidean inputDimension) (ComplexEuclidean outputDimension)) :
    ACore parameters inputDimension →ₗ[ℂ] ACore parameters inputDimension →ₗ[ℂ]
      ACore parameters outputDimension :=
  LinearMap.mk₂ ℂ
    (fun first second => actualMultilinearProduct parameters multiplication ![first, second])
    (fun firstOne firstTwo second => by
      have expand := actualMultilinearProduct_update_add (parameters := parameters)
        multiplication ![firstOne, second] 0 firstOne firstTwo
      rwa [pair_update_zero, pair_update_zero, pair_update_zero] at expand)
    (fun scalar first second => by
      have expand := actualMultilinearProduct_update_smul (parameters := parameters)
        multiplication ![first, second] 0 scalar first
      rwa [pair_update_zero, pair_update_zero] at expand)
    (fun first secondOne secondTwo => by
      have expand := actualMultilinearProduct_update_add (parameters := parameters)
        multiplication ![first, secondOne] 1 secondOne secondTwo
      rwa [pair_update_one, pair_update_one, pair_update_one] at expand)
    (fun scalar first second => by
      have expand := actualMultilinearProduct_update_smul (parameters := parameters)
        multiplication ![first, second] 1 scalar second
      rwa [pair_update_one, pair_update_one] at expand)

@[simp] theorem pairProductLinear_apply {outputDimension inputDimension : ℕ}
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin 2 => ComplexEuclidean inputDimension) (ComplexEuclidean outputDimension))
    (first second : ACore parameters inputDimension) :
    pairProductLinear parameters multiplication first second =
      actualMultilinearProduct parameters multiplication ![first, second] := rfl

/-- The third slot of the actual trilinear physical product. -/
def tripleThirdLinear {outputDimension inputDimension : ℕ} (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin 3 => ComplexEuclidean inputDimension) (ComplexEuclidean outputDimension))
    (first second : ACore parameters inputDimension) :
    ACore parameters inputDimension →ₗ[ℂ] ACore parameters outputDimension where
  toFun third := actualMultilinearProduct parameters multiplication ![first, second, third]
  map_add' thirdOne thirdTwo := by
    have expand := actualMultilinearProduct_update_add (parameters := parameters)
      multiplication ![first, second, thirdOne] 2 thirdOne thirdTwo
    rwa [triple_update_two, triple_update_two, triple_update_two] at expand
  map_smul' scalar third := by
    have expand := actualMultilinearProduct_update_smul (parameters := parameters)
      multiplication ![first, second, third] 2 scalar third
    rwa [triple_update_two, triple_update_two] at expand

/-- The actual trilinear physical product, curried into complex-linear slots. -/
def tripleProductLinear {outputDimension inputDimension : ℕ} (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin 3 => ComplexEuclidean inputDimension) (ComplexEuclidean outputDimension)) :
    ACore parameters inputDimension →ₗ[ℂ] ACore parameters inputDimension →ₗ[ℂ]
      ACore parameters inputDimension →ₗ[ℂ] ACore parameters outputDimension :=
  LinearMap.mk₂ ℂ (fun first second => tripleThirdLinear parameters multiplication first second)
    (fun firstOne firstTwo second => by
      apply LinearMap.ext
      intro third
      have expand := actualMultilinearProduct_update_add (parameters := parameters)
        multiplication ![firstOne, second, third] 0 firstOne firstTwo
      rw [triple_update_zero, triple_update_zero, triple_update_zero] at expand
      exact expand)
    (fun scalar first second => by
      apply LinearMap.ext
      intro third
      have expand := actualMultilinearProduct_update_smul (parameters := parameters)
        multiplication ![first, second, third] 0 scalar first
      rw [triple_update_zero, triple_update_zero] at expand
      exact expand)
    (fun first secondOne secondTwo => by
      apply LinearMap.ext
      intro third
      have expand := actualMultilinearProduct_update_add (parameters := parameters)
        multiplication ![first, secondOne, third] 1 secondOne secondTwo
      rw [triple_update_one, triple_update_one, triple_update_one] at expand
      exact expand)
    (fun scalar first second => by
      apply LinearMap.ext
      intro third
      have expand := actualMultilinearProduct_update_smul (parameters := parameters)
        multiplication ![first, second, third] 1 scalar second
      rw [triple_update_one, triple_update_one] at expand
      exact expand)

@[simp] theorem tripleProductLinear_apply {outputDimension inputDimension : ℕ}
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin 3 => ComplexEuclidean inputDimension) (ComplexEuclidean outputDimension))
    (first second third : ACore parameters inputDimension) :
    tripleProductLinear parameters multiplication first second third =
      actualMultilinearProduct parameters multiplication ![first, second, third] := rfl

end Grad.NonlinearQuotientBounds
