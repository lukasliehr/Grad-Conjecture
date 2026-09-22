import AKU46ActualScalarAndFiniteForce
import AKU44ActualLiftCovectorRecovery

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.QuotientProjection Grad.FlatSourceProjection

theorem timeDerivativeCore_coordinate {parameters : PhaseParameters} {dimension : ℕ}
    (coordinate : Fin 2) (field : ACore parameters dimension) :
    timeDerivativeCore parameters (coordinateCore parameters coordinate field) =
      coordinateCore parameters coordinate (timeDerivativeCore parameters field) := by
  apply acore_ext
  intro cell point
  rw [timeDerivativeCore_val,coordinateCore_val,coordinateCore_val,timeDerivativeCore_val]
  simp only [closedJet_value_smul,ContinuousMap.smul_apply,coordinateJet_value]
  exact smul_comm _ _ _

theorem valueMapCore_coordinate {parameters : PhaseParameters} {input output : ℕ}
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (coordinate : Fin 2) (field : ACore parameters input) :
    valueMapCore parameters mapping (coordinateCore parameters coordinate field) =
      coordinateCore parameters coordinate (valueMapCore parameters mapping field) := by
  apply coreValue_ext
  intro point angle
  rw [coreValue_valueMap,coreValue_coordinate,coreValue_coordinate,coreValue_valueMap]
  exact mapping.map_smul_of_tower _ _

theorem physicalVariationAffine_coordinate {parameters : PhaseParameters}
    (epsilon : ℂ) (coordinate : Fin 2) (field : ACore parameters 3) :
    physicalVariationAffine epsilon (coordinateCore parameters coordinate field) =
      coordinateCore parameters coordinate (physicalVariationAffine epsilon field) := by
  rw [physicalVariationAffine,timeDerivativeCore_coordinate,valueMapCore_coordinate,
    physicalVariationAffine,map_add,map_smul]

theorem traceZero_timeDerivative_of_zero {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (vanishes : traceZero field = 0) :
    traceZero (timeDerivativeCore parameters field) = 0 := by
  apply Subtype.ext
  funext cell
  rw [traceZero_val,timeDerivativeCore_val,originValue_smul]
  have zero : originValue (field.val cell) = 0 :=
    congrArg (fun data : Grad.AxisCore.AxisSmoothCore parameters dimension => data.val cell) vanishes
  rw [zero,smul_zero]
  rfl

theorem traceZero_valueMap_of_zero {parameters : PhaseParameters} {input output : ℕ}
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (field : ACore parameters input) (vanishes : traceZero field = 0) :
    traceZero (valueMapCore parameters mapping field) = 0 := by
  apply Subtype.ext
  funext cell
  rw [traceZero_val,valueMapCore_originValue]
  have zero : originValue (field.val cell) = 0 :=
    congrArg (fun data : Grad.AxisCore.AxisSmoothCore parameters input => data.val cell) vanishes
  rw [zero,map_zero]
  rfl

theorem affineStateCore_axis (parameters : PhaseParameters) (length : ℝ) (base : QuotientState parameters)
    (vanishes : traceZero base.2.1 = 0) :
    traceZero (affineStateCore parameters length base) = (length : ℂ) • traceZero (eTConstantCore parameters) := by
  change traceZero (timeDerivativeCore parameters base.2.1 +
    base.1 • valueMapCore parameters tangentGeneratorMap base.2.1 + (length : ℂ) • eTConstantCore parameters) = _
  rw [map_add,map_add,map_smul,map_smul]
  rw [traceZero_timeDerivative_of_zero _ vanishes,traceZero_valueMap_of_zero _ _ vanishes]
  simp

theorem secondTaylorAxis_rotation_dot_axial_quadratic {parameters : PhaseParameters}
    (epsilon : ℂ) (field coefficient : ACore parameters 3) (outer inner : Fin 2) :
    secondTaylorAxis (dotOperation parameters (rotationCore parameters field)
      (physicalVariationAffine epsilon (coordinateCore parameters outer (coordinateCore parameters inner coefficient)))) = 0 := by
  rw [physicalVariationAffine_coordinate,physicalVariationAffine_coordinate]
  funext index
  fin_cases index <;> simp [rotationCore,secondTaylorAxis,map_sub,dot_coordinate_first,dot_coordinate_second,
    secondAxisTrace_two_coordinates,traceZero_coordinateCore]

theorem secondTaylorAxis_rotation_dot_actual_axial_lift {parameters : PhaseParameters}
    (epsilon : ℂ) (field : ACore parameters 3) (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters 3) :
    secondTaylorAxis (dotOperation parameters (rotationCore parameters field)
      (physicalVariationAffine epsilon (localizedQuadraticVectorAxisCore data))) = 0 := by
  rw [localizedQuadraticVectorAxisCore_coordinates]
  have additive (first second : ACore parameters 3) :
      physicalVariationAffine epsilon (first+second) = physicalVariationAffine epsilon first + physicalVariationAffine epsilon second := by
    simp only [physicalVariationAffine,map_add,smul_add]
    abel
  rw [additive,additive]
  simp only [map_add,secondTaylorAxis_add,secondTaylorAxis_rotation_dot_axial_quadratic,add_zero]

end Grad.FinitePhysicalJetLift
