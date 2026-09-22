import AKU34AxisPhysicalCoreFidelity
import AKU33OriginalCoordinateProductFactors

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearDivision

def constantValueJetLinear (dimension : ℕ) : ComplexEuclidean dimension →ₗ[ℂ] ClosedJet dimension where
  toFun := constantValueJet
  map_add' first second := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    simp only [constantValueJet_value,closedJet_value_add,ContinuousMap.add_apply]
  map_smul' scalar value := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    simp only [constantValueJet_value,closedJet_value_smul,ContinuousMap.smul_apply,RingHom.id_apply]

def axisConstantCore {parameters : PhaseParameters} {dimension : ℕ}
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) : ACore parameters dimension :=
  vectorAxisProfileCore (constantValueJetLinear dimension) data

def localizedAxisConstantCore {parameters : PhaseParameters} {dimension : ℕ}
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) : ACore parameters dimension :=
  vectorAxisProfileCore ((localizedFiniteJetLinear dimension).comp (constantValueJetLinear dimension)) data

theorem axisConstantCore_val {parameters : PhaseParameters} {dimension : ℕ}
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) (cell : ℤ) :
    (axisConstantCore data).val cell = constantValueJet (data.val cell) :=
  vectorAxisProfileCore_val _ data cell

theorem localizedAxisConstantCore_val {parameters : PhaseParameters} {dimension : ℕ}
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) (cell : ℤ) :
    (localizedAxisConstantCore data).val cell = localizedFiniteJet (constantValueJet (data.val cell)) :=
  vectorAxisProfileCore_val _ data cell

theorem traceZero_axisConstantCore {parameters : PhaseParameters} {dimension : ℕ}
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) : traceZero (axisConstantCore data) = data := by
  apply Subtype.ext
  funext cell
  rw [traceZero_val,axisConstantCore_val,originValue,constantValueJet_value]

theorem traceZero_localizedAxisConstantCore {parameters : PhaseParameters} {dimension : ℕ}
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) : traceZero (localizedAxisConstantCore data) = data := by
  apply Subtype.ext
  funext cell
  rw [traceZero_val,localizedAxisConstantCore_val,originValue]
  change (localizedFiniteJet _).value closedOrigin = _
  rw [localizedFiniteJet_origin,constantValueJet_value]

theorem traceFirst_localizedAxisConstantCore {parameters : PhaseParameters} {dimension : ℕ}
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) (direction : Fin 2) :
    traceFirst direction (localizedAxisConstantCore data) = 0 := by
  apply Subtype.ext
  funext cell
  rw [traceFirst_val,localizedAxisConstantCore_val,localizedFiniteJet_originPartial]
  exact partial_constantValueJet_value direction (data.val cell) closedOrigin

/-- The original cutoff polynomial is literally a sum of coordinate
products. Taylor order is therefore proved algebraically inside ACore. -/
theorem localizedQuadraticVectorAxisCore_coordinates {parameters : PhaseParameters} {dimension : ℕ}
    (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters dimension) :
    localizedQuadraticVectorAxisCore data =
      coordinateCore parameters 0 (coordinateCore parameters 0 (localizedAxisConstantCore (data 0))) +
      coordinateCore parameters 0 (coordinateCore parameters 1 (localizedAxisConstantCore (data 1))) +
      coordinateCore parameters 1 (coordinateCore parameters 1 (localizedAxisConstantCore (data 2))) := by
  apply acore_ext
  intro cell point
  rw [localizedQuadraticVectorAxisCore_val,localizedFiniteJet_value,quadraticVectorJet_value]
  simp only [acore_add_value,coordinateCore_val,coordinateJet_value,localizedAxisConstantCore_val,
    localizedFiniteJet_value,constantValueJet_value,smul_add,smul_smul,pow_two]
  module

theorem secondTaylorAxis_localizedQuadraticVectorAxisCore {parameters : PhaseParameters} {dimension : ℕ}
    (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters dimension) :
    secondTaylorAxis (localizedQuadraticVectorAxisCore data) = data := by
  rw [localizedQuadraticVectorAxisCore_coordinates]
  funext index
  fin_cases index <;> simp [secondTaylorAxis,map_add,secondAxisTrace_two_coordinates,
    traceZero_localizedAxisConstantCore]
  all_goals module

end Grad.FinitePhysicalJetLift
