import AKU39CurrentForceTaylorLocality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct

theorem secondAxisTrace_partial_remainder_rotation_lift {parameters : PhaseParameters}
    (field : ACore parameters 3) (vanishes : ∀ direction, traceFirst direction field = 0)
    (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters 3) (direction first second : Fin 2) :
    secondAxisTrace first second (dotOperation parameters (partialCore parameters direction field)
      (rotationCore parameters (localizedQuadraticVectorAxisCore data))) = 0 := by
  rw [localizedQuadraticVectorAxisCore_coordinates]
  simp only [map_add,
    secondAxisTrace_partial_remainder_rotation_quadratic field _ vanishes,add_zero]

theorem secondAxisTrace_partial_lift_rotation_remainder {parameters : PhaseParameters}
    (field : ACore parameters 3) (vanishes : ∀ direction, traceFirst direction field = 0)
    (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters 3) (direction first second : Fin 2) :
    secondAxisTrace first second (dotOperation parameters
      (partialCore parameters direction (localizedQuadraticVectorAxisCore data)) (rotationCore parameters field)) = 0 := by
  rw [localizedQuadraticVectorAxisCore_coordinates]
  simp only [map_add,LinearMap.add_apply,
    secondAxisTrace_partial_quadratic_rotation_remainder field _ vanishes,add_zero]

/-- The genuine variable-current force has the same quadratic Taylor
coefficient as its exact first Taylor field. This is an equality for the
original operator on the actual localized vector, without a remainder premise. -/
theorem actualCurrentForce_secondTaylor (parameters : PhaseParameters)
    (field : ACore parameters 3) (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters 3)
    (scalar : ACore parameters 1) (direction : Fin 2) :
    secondTaylorAxis (physicalCartesianForceComponent direction field
      (localizedQuadraticVectorAxisCore data) scalar) =
      secondTaylorAxis (physicalCartesianForceComponent direction (originalLinearTaylorCore field)
        (localizedQuadraticVectorAxisCore data) scalar) := by
  rw [localizedQuadraticForce_secondTaylor,localizedQuadraticForce_secondTaylor]
  have vanishes : ∀ coordinate, traceFirst coordinate (field-originalLinearTaylorCore field) = 0 :=
    originalLinearTaylorCore_remainder_first field
  have left (first second : Fin 2) :
      secondAxisTrace first second (dotOperation parameters (partialCore parameters direction field)
        (rotationCore parameters (localizedQuadraticVectorAxisCore data))) =
      secondAxisTrace first second (dotOperation parameters (partialCore parameters direction (originalLinearTaylorCore field))
        (rotationCore parameters (localizedQuadraticVectorAxisCore data))) := by
    have zero := secondAxisTrace_partial_remainder_rotation_lift _ vanishes data direction first second
    simpa only [map_sub,LinearMap.sub_apply,sub_eq_zero] using zero
  have right (first second : Fin 2) :
      secondAxisTrace first second (dotOperation parameters
        (partialCore parameters direction (localizedQuadraticVectorAxisCore data)) (rotationCore parameters field)) =
      secondAxisTrace first second (dotOperation parameters
        (partialCore parameters direction (localizedQuadraticVectorAxisCore data))
          (rotationCore parameters (originalLinearTaylorCore field))) := by
    have zero := secondAxisTrace_partial_lift_rotation_remainder _ vanishes data direction first second
    simpa only [map_sub,sub_eq_zero] using zero
  funext index
  fin_cases index <;> simp only [secondTaylorAxis,map_sub,left,right]

end Grad.FinitePhysicalJetLift
