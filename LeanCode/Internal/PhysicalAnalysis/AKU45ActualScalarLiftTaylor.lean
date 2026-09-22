import AKU42ExactQuadraticForceProducts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision

theorem secondTaylorAxis_partial_localizedQuadratic {parameters : PhaseParameters} {dimension : ℕ}
    (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters dimension) (direction : Fin 2) :
    secondTaylorAxis (partialCore parameters direction (localizedQuadraticVectorAxisCore data)) = 0 := by
  rw [localizedQuadraticVectorAxisCore_coordinates]
  funext index
  fin_cases direction <;> fin_cases index
  all_goals simp [partialCore_coordinateCore,secondTaylorAxis,map_add,
    secondAxisTrace_coordinate,traceFirst_coordinateCore,traceZero_partialCore,
    traceFirst_localizedAxisConstantCore]

theorem localizedCubicScalarAxisCore_coordinates {parameters : PhaseParameters}
    (data : Fin 4 → Grad.AxisCore.AxisSmoothCore parameters 1) :
    localizedCubicScalarAxisCore data =
      coordinateCore parameters 0 (coordinateCore parameters 0 (coordinateCore parameters 0 (localizedAxisConstantCore (data 0)))) +
      coordinateCore parameters 0 (coordinateCore parameters 0 (coordinateCore parameters 1 (localizedAxisConstantCore (data 1)))) +
      coordinateCore parameters 0 (coordinateCore parameters 1 (coordinateCore parameters 1 (localizedAxisConstantCore (data 2)))) +
      coordinateCore parameters 1 (coordinateCore parameters 1 (coordinateCore parameters 1 (localizedAxisConstantCore (data 3)))) := by
  apply acore_ext
  intro cell point
  rw [localizedCubicScalarAxisCore_val,localizedFiniteJet_value]
  apply PiLp.ext
  intro component
  have only : component = 0 := Subsingleton.elim _ _
  subst component
  simp only [cubicScalarJet_value,acore_add_value,coordinateCore_val,coordinateJet_value,
    localizedAxisConstantCore_val,localizedFiniteJet_value,constantValueJet_value,
    PiLp.add_apply,PiLp.smul_apply,Complex.real_smul]
  ring

theorem secondTaylorAxis_partial_localizedCubic {parameters : PhaseParameters}
    (data : Fin 4 → Grad.AxisCore.AxisSmoothCore parameters 1) (direction : Fin 2) :
    secondTaylorAxis (partialCore parameters direction (localizedCubicScalarAxisCore data)) =
      if direction = 0 then ![(3 : ℂ) • data 0,(2 : ℂ) • data 1,data 2]
      else ![data 1,(2 : ℂ) • data 2,(3 : ℂ) • data 3] := by
  rw [localizedCubicScalarAxisCore_coordinates]
  funext index
  fin_cases direction <;> fin_cases index
  all_goals simp [partialCore_coordinateCore,secondTaylorAxis,map_add,
    secondAxisTrace_two_coordinates,traceZero_coordinateCore,traceZero_localizedAxisConstantCore]
  all_goals module

end Grad.FinitePhysicalJetLift
