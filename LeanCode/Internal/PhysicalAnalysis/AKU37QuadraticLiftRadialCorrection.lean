import AKU36ActualRadialCorrectionAxisJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct

theorem dot_coordinate_first {parameters : PhaseParameters}
    (coordinate : Fin 2) (first second : ACore parameters 3) :
    dotOperation parameters (coordinateCore parameters coordinate first) second =
      coordinateCore parameters coordinate (dotOperation parameters first second) :=
  pairProduct_coordinate_left physicalDotProduct coordinate first second

theorem dot_coordinate_second {parameters : PhaseParameters}
    (coordinate : Fin 2) (first second : ACore parameters 3) :
    dotOperation parameters first (coordinateCore parameters coordinate second) =
      coordinateCore parameters coordinate (dotOperation parameters first second) :=
  pairProduct_coordinate_right physicalDotProduct coordinate first second

/-- The complete Euler/angular product has at least three genuine coordinate
factors when the varied vector is quadratic, even with variable cutoff coefficients. -/
theorem secondAxisTrace_euler_quadratic_rotation {parameters : PhaseParameters}
    (field coefficient : ACore parameters 3) (outer inner first second : Fin 2) :
    secondAxisTrace first second (dotOperation parameters
      (eulerCore parameters (coordinateCore parameters outer (coordinateCore parameters inner coefficient)))
      (rotationCore parameters field)) = 0 := by
  fin_cases outer <;> fin_cases inner
  all_goals simp [eulerCore,rotationCore,partialCore_coordinateCore,map_add,map_sub,
    dot_coordinate_first,dot_coordinate_second,secondAxisTrace_three_coordinates]

theorem secondAxisTrace_euler_rotation_quadratic {parameters : PhaseParameters}
    (field coefficient : ACore parameters 3) (outer inner first second : Fin 2) :
    secondAxisTrace first second (dotOperation parameters (eulerCore parameters field)
      (rotationCore parameters (coordinateCore parameters outer (coordinateCore parameters inner coefficient)))) = 0 := by
  fin_cases outer <;> fin_cases inner
  all_goals simp [eulerCore,rotationCore,partialCore_coordinateCore,map_add,map_sub,
    dot_coordinate_first,dot_coordinate_second,secondAxisTrace_three_coordinates]

theorem physicalVariationRadialCorrection_post {parameters : PhaseParameters}
    (field vector : ACore parameters 3) :
    physicalVariationRadialCorrection field vector = radialQuotientPost parameters
      (dotOperation parameters (eulerCore parameters vector) (rotationCore parameters field) +
        dotOperation parameters (eulerCore parameters field) (rotationCore parameters vector)) := by
  rw [map_add]
  rfl

theorem quadraticVariationRadialCorrection_zero_jets {parameters : PhaseParameters}
    (field coefficient : ACore parameters 3) (outer inner : Fin 2) :
    traceZero (physicalVariationRadialCorrection field
      (coordinateCore parameters outer (coordinateCore parameters inner coefficient))) = 0 ∧
      ∀ direction, traceFirst direction (physicalVariationRadialCorrection field
        (coordinateCore parameters outer (coordinateCore parameters inner coefficient))) = 0 := by
  rw [physicalVariationRadialCorrection_post]
  constructor
  · apply radialQuotientPost_origin_zero
    intro first second
    rw [map_add,secondAxisTrace_euler_quadratic_rotation,secondAxisTrace_euler_rotation_quadratic,add_zero]
  · exact fun direction => radialQuotientPost_first_zero _ direction

theorem physicalVariationRadialCorrection_add {parameters : PhaseParameters}
    (field first second : ACore parameters 3) :
    physicalVariationRadialCorrection field (first+second) =
      physicalVariationRadialCorrection field first + physicalVariationRadialCorrection field second := by
  simp only [physicalVariationRadialCorrection,map_add,LinearMap.add_apply]
  abel

/-- The exact original radial correction contributes neither a constant nor
linear axis coefficient for the actual localized quadratic vector. -/
theorem localizedQuadraticRadialCorrection_zero_jets {parameters : PhaseParameters}
    (field : ACore parameters 3) (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters 3) :
    traceZero (physicalVariationRadialCorrection field (localizedQuadraticVectorAxisCore data)) = 0 ∧
      ∀ direction, traceFirst direction
        (physicalVariationRadialCorrection field (localizedQuadraticVectorAxisCore data)) = 0 := by
  rw [localizedQuadraticVectorAxisCore_coordinates,physicalVariationRadialCorrection_add,physicalVariationRadialCorrection_add]
  constructor
  · rw [map_add,map_add,(quadraticVariationRadialCorrection_zero_jets field _ 0 0).1,
      (quadraticVariationRadialCorrection_zero_jets field _ 0 1).1,
      (quadraticVariationRadialCorrection_zero_jets field _ 1 1).1,add_zero,add_zero]
  · intro direction
    rw [map_add,map_add,(quadraticVariationRadialCorrection_zero_jets field _ 0 0).2 direction,
      (quadraticVariationRadialCorrection_zero_jets field _ 0 1).2 direction,
      (quadraticVariationRadialCorrection_zero_jets field _ 1 1).2 direction,add_zero,add_zero]


/-- The original projected force has exactly the same quadratic Taylor
coefficient as its unreduced Cartesian differential terms on this lift.
The radial correction is eliminated by the proved actual axis identities. -/
theorem localizedQuadraticForce_secondTaylor {parameters : PhaseParameters}
    (field : ACore parameters 3) (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters 3)
    (scalar : ACore parameters 1) (direction : Fin 2) :
    secondTaylorAxis (physicalCartesianForceComponent direction field
      (localizedQuadraticVectorAxisCore data) scalar) =
      secondTaylorAxis (partialCore parameters direction scalar -
        dotOperation parameters (partialCore parameters direction (localizedQuadraticVectorAxisCore data))
          (rotationCore parameters field) -
        dotOperation parameters (partialCore parameters direction field)
          (rotationCore parameters (localizedQuadraticVectorAxisCore data))) := by
  have first := (localizedQuadraticRadialCorrection_zero_jets field data).2
  funext index
  fin_cases index <;> simp [physicalCartesianForceComponent,secondTaylorAxis,map_add,
    secondAxisTrace_coordinate,first]

theorem localizedQuadraticForce_firstTrace {parameters : PhaseParameters}
    (field : ACore parameters 3) (data : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters 3)
    (scalar : ACore parameters 1) (direction derivative : Fin 2) :
    traceFirst derivative (physicalCartesianForceComponent direction field
      (localizedQuadraticVectorAxisCore data) scalar) =
      traceFirst derivative (partialCore parameters direction scalar -
        dotOperation parameters (partialCore parameters direction (localizedQuadraticVectorAxisCore data))
          (rotationCore parameters field) -
        dotOperation parameters (partialCore parameters direction field)
          (rotationCore parameters (localizedQuadraticVectorAxisCore data))) := by
  rw [physicalCartesianForceComponent,map_add,traceFirst_coordinateCore,
    (localizedQuadraticRadialCorrection_zero_jets field data).1]
  split_ifs <;> simp

end Grad.FinitePhysicalJetLift
