import QP4ProjectionLaws
import AxisProductOrigin

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.NonlinearRange

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.AxisSplit Grad.AxisJet Grad.QuotientProjection

variable {parameters : PhaseParameters}

/-- Coordinate multiplication moves through the second physical product
slot, without changing the Fourier convolution or inserting conjugates. -/
theorem pairProduct_coordinate_right {inputDimension outputDimension : ℕ}
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin 2 => ComplexEuclidean inputDimension) (ComplexEuclidean outputDimension))
    (coordinate : Fin 2) (first second : ACore parameters inputDimension) :
    pairProductLinear parameters multiplication first (coordinateCore parameters coordinate second) =
      coordinateCore parameters coordinate (pairProductLinear parameters multiplication first second) := by
  apply acore_ext
  intro cell point
  rw [pairProductLinear_apply, pairProductLinear_apply,
    actualMultilinearProduct_isActual parameters multiplication _ cell point]
  have rightSide : ((coordinateCore parameters coordinate
      (actualMultilinearProduct parameters multiplication ![first, second])).val cell).value point =
      point.val coordinate • productCoefficientValue multiplication ![first, second] cell point := by
    rw [coordinateCore_val, coordinateJet_value,
      actualMultilinearProduct_isActual parameters multiplication _ cell point]
  rw [rightSide]
  unfold productCoefficientValue
  rw [← tsum_const_smul'' (point.val coordinate)]
  apply tsum_congr
  intro cells
  have tuple : (fun index =>
      ((![first, coordinateCore parameters coordinate second] index).val (cells.val index)).value point) =
      Function.update (fun index => ((![first, second] index).val (cells.val index)).value point) 1
        (point.val coordinate • ((second.val (cells.val 1)).value point)) := by
    funext index
    fin_cases index
    · rfl
    · change ((coordinateCore parameters coordinate second).val (cells.val 1)).value point = _
      rw [coordinateCore_val, coordinateJet_value]
      rfl
  rw [tuple, ← Complex.coe_smul, multiplication.map_update_smul]
  have unchanged : Function.update (fun index =>
      ((![first, second] index).val (cells.val index)).value point) 1
      ((second.val (cells.val 1)).value point) = fun index =>
        ((![first, second] index).val (cells.val index)).value point := by
    funext index
    fin_cases index <;> rfl
  rw [unchanged]
  exact (Complex.coe_smul _ _).trans rfl

theorem traceFirst_coordinateCore {dimension : ℕ} (direction coordinate : Fin 2)
    (field : ACore parameters dimension) :
    traceFirst direction (coordinateCore parameters coordinate field) =
      if direction = coordinate then traceZero field else 0 := by
  apply Subtype.ext
  funext cell
  rw [traceFirst_val, coordinateCore_val, coordinateJet_originPartial]
  by_cases same : direction = coordinate
  · rw [if_pos same, if_pos same, traceZero_val]
  · rw [if_neg same, if_neg same]
    rfl

theorem traceFirst_dot_rotation_zero (first second : ACore parameters 3) :
    traceFirst 0 (dotOperation parameters first (rotationCore parameters second)) =
      traceZero (dotOperation parameters first (partialCore parameters 1 second)) := by
  change traceFirst 0 (pairProductLinear parameters physicalDotProduct first
    (coordinateCore parameters 0 (partialCore parameters 1 second) -
      coordinateCore parameters 1 (partialCore parameters 0 second))) = _
  rw [map_sub, pairProduct_coordinate_right, pairProduct_coordinate_right, map_sub,
    traceFirst_coordinateCore, traceFirst_coordinateCore,
    if_pos rfl, if_neg (by decide : ¬(0 : Fin 2) = 1), sub_zero]
  rfl

theorem traceFirst_dot_rotation_one (first second : ACore parameters 3) :
    traceFirst 1 (dotOperation parameters first (rotationCore parameters second)) =
      -traceZero (dotOperation parameters first (partialCore parameters 0 second)) := by
  change traceFirst 1 (pairProductLinear parameters physicalDotProduct first
    (coordinateCore parameters 0 (partialCore parameters 1 second) -
      coordinateCore parameters 1 (partialCore parameters 0 second))) = _
  rw [map_sub, pairProduct_coordinate_right, pairProduct_coordinate_right, map_sub,
    traceFirst_coordinateCore, traceFirst_coordinateCore,
    if_neg (by decide : ¬(1 : Fin 2) = 0), if_pos rfl, zero_sub]
  rfl

theorem partialCore_commute {dimension : ℕ} (first second : Fin 2)
    (field : ACore parameters dimension) :
    partialCore parameters first (partialCore parameters second field) =
      partialCore parameters second (partialCore parameters first field) := by
  apply acore_ext
  intro cell point
  change closedDerivative (partialJet second (field.val cell)) 1 (fun _ => first) point =
    closedDerivative (partialJet first (field.val cell)) 1 (fun _ => second) point
  rw [partialJet_closedDerivative, partialJet_closedDerivative,
    closedDerivative_eq_multi, closedDerivative_eq_multi]
  congr 2
  fin_cases first <;> fin_cases second <;> decide

theorem traceFirst_partialCore_commute {dimension : ℕ} (first second : Fin 2)
    (field : ACore parameters dimension) :
    traceFirst first (partialCore parameters second field) =
      traceFirst second (partialCore parameters first field) := by
  change traceZero (partialCore parameters first (partialCore parameters second field)) =
    traceZero (partialCore parameters second (partialCore parameters first field))
  rw [partialCore_commute]

theorem angularCore_removeAngularCore {dimension : ℕ} (field : ACore parameters dimension) :
    angularCore parameters 0 (removeAngularCore parameters field) = 0 := by
  change angularCore parameters 0 (field - angularCore parameters 0 field) = 0
  rw [map_sub, angularCore_projection, if_pos rfl, sub_self]

theorem quotientPolynomialRows_third_mean (cellLength : ℝ) (state : QuotientState parameters) :
    angularCore parameters 0 (quotientPolynomialRows parameters cellLength state 2) = 0 := by
  exact angularCore_removeAngularCore (determinantOperation parameters
    (partialCore parameters 0 (stateField state)) (partialCore parameters 1 (stateField state))
    (affineStateCore parameters cellLength state))

theorem quotientPolynomialRows_fourth_mean (cellLength : ℝ) (state : QuotientState parameters) :
    angularCore parameters 0 (quotientPolynomialRows parameters cellLength state 3) = 0 := by
  exact angularCore_removeAngularCore (dotOperation parameters (rotationCore parameters (stateField state))
    (affineStateCore parameters cellLength state) - timeDerivativeCore parameters (statePotential state))

end Grad.NonlinearRange
