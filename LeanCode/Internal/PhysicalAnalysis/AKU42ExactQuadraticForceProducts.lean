import AKU41ActualAxisCurrentProducts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct

theorem secondTaylorAxis_current_partial_rotation_lift {parameters : PhaseParameters}
    (field : ACore parameters 3) (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters 3)
    (direction : Fin 2) :
    secondTaylorAxis (dotOperation parameters (partialCore parameters direction (originalLinearTaylorCore field))
      (rotationCore parameters (localizedQuadraticVectorAxisCore data))) =
      ![axisDot (traceFirst direction field) (data 1),
        (2 : ℂ) • axisDot (traceFirst direction field) (data 2) - (2 : ℂ) • axisDot (traceFirst direction field) (data 0),
        -(axisDot (traceFirst direction field) (data 1))] := by
  rw [localizedQuadraticVectorAxisCore_coordinates]
  funext index
  fin_cases direction <;> fin_cases index
  all_goals simp [originalLinearTaylorCore,partialCore_coordinateCore,partialCore_axisConstantCore,
    rotationCore,secondTaylorAxis,map_add,map_sub,dot_coordinate_second,
    secondAxisTrace_two_coordinates,traceZero_coordinateCore,traceZero_dot_eq_axisDot,
    traceZero_axisConstantCore,traceZero_localizedAxisConstantCore]
  all_goals module

theorem secondTaylorAxis_lift_partial_current_rotation {parameters : PhaseParameters}
    (field : ACore parameters 3) (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters 3)
    (direction : Fin 2) :
    secondTaylorAxis (dotOperation parameters
      (partialCore parameters direction (localizedQuadraticVectorAxisCore data))
      (rotationCore parameters (originalLinearTaylorCore field))) =
      if direction = 0 then
        ![(2 : ℂ) • axisDot (data 0) (traceFirst 1 field),
          axisDot (data 1) (traceFirst 1 field) - (2 : ℂ) • axisDot (data 0) (traceFirst 0 field),
          -(axisDot (data 1) (traceFirst 0 field))]
      else
        ![axisDot (data 1) (traceFirst 1 field),
          (2 : ℂ) • axisDot (data 2) (traceFirst 1 field) - axisDot (data 1) (traceFirst 0 field),
          -(2 : ℂ) • axisDot (data 2) (traceFirst 0 field)] := by
  rw [localizedQuadraticVectorAxisCore_coordinates]
  funext index
  fin_cases direction <;> fin_cases index
  all_goals simp [originalLinearTaylorCore,partialCore_coordinateCore,partialCore_axisConstantCore,
    rotationCore,secondTaylorAxis,map_add,dot_coordinate_first,dot_coordinate_second,
    secondAxisTrace_two_coordinates,traceZero_coordinateCore,traceZero_dot_eq_axisDot,
    traceZero_axisConstantCore,traceZero_localizedAxisConstantCore]
  all_goals module

end Grad.FinitePhysicalJetLift
