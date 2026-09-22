import AKU49ActualAxialCorrectionOrder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct

theorem traceFirst_determinant_partial_lift_first {parameters : PhaseParameters}
    (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters 3) (second third : ACore parameters 3)
    (direction : Fin 2) :
    traceFirst direction (determinantOperation parameters
      (partialCore parameters 0 (localizedQuadraticVectorAxisCore data)) second third) =
      if direction = 0 then (2 : ℂ) • traceZero
        (determinantOperation parameters (localizedAxisConstantCore (data 0)) second third)
      else traceZero (determinantOperation parameters (localizedAxisConstantCore (data 1)) second third) := by
  rw [localizedQuadraticVectorAxisCore_coordinates]
  fin_cases direction <;> simp [partialCore_coordinateCore,map_add,LinearMap.add_apply,
    determinant_coordinate_first,traceFirst_coordinateCore,traceZero_coordinateCore]
  module

theorem traceFirst_determinant_partial_lift_second {parameters : PhaseParameters}
    (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters 3) (first third : ACore parameters 3)
    (direction : Fin 2) :
    traceFirst direction (determinantOperation parameters first
      (partialCore parameters 1 (localizedQuadraticVectorAxisCore data)) third) =
      if direction = 0 then traceZero (determinantOperation parameters first (localizedAxisConstantCore (data 1)) third)
      else (2 : ℂ) • traceZero (determinantOperation parameters first (localizedAxisConstantCore (data 2)) third) := by
  rw [localizedQuadraticVectorAxisCore_coordinates]
  fin_cases direction <;> simp [partialCore_coordinateCore,map_add,LinearMap.add_apply,
    determinant_coordinate_second,traceFirst_coordinateCore,traceZero_coordinateCore]
  module

theorem traceFirst_determinant_actual_axial_lift_zero {parameters : PhaseParameters}
    (epsilon : ℂ) (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters 3)
    (first second : ACore parameters 3) (direction : Fin 2) :
    traceFirst direction (determinantOperation parameters first second
      (physicalVariationAffine epsilon (localizedQuadraticVectorAxisCore data))) = 0 := by
  rw [localizedQuadraticVectorAxisCore_coordinates]
  have additive (a b : ACore parameters 3) :
      physicalVariationAffine epsilon (a+b) = physicalVariationAffine epsilon a + physicalVariationAffine epsilon b := by
    simp only [physicalVariationAffine,map_add,smul_add]
    abel
  rw [additive,additive]
  fin_cases direction <;> simp [physicalVariationAffine_coordinate,map_add,determinant_coordinate_third,
    traceFirst_coordinateCore,traceZero_coordinateCore]

theorem traceFirst_removeAngular {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (direction : Fin 2) :
    traceFirst direction (removeAngularCore parameters field) = traceFirst direction field := by
  change traceFirst direction (field-angularCore parameters 0 field) = _
  rw [map_sub]
  have zero : traceFirst direction (angularCore parameters 0 field) = 0 := by
    apply Subtype.ext
    funext cell
    rw [traceFirst_val]
    change originPartial direction (angularClosedJet 0 (field.val cell)) = 0
    exact angularJet_zero_originPartial direction (field.val cell)
  rw [zero,sub_zero]

end Grad.FinitePhysicalJetLift
