import AKU37QuadraticLiftRadialCorrection
import AKU38ActualAxisProductZeros

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct

theorem traceZero_partialCore {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (direction : Fin 2) :
    traceZero (partialCore parameters direction field) = traceFirst direction field := rfl

/-- Current-coefficient terms with an actual zero first axis trace make no
quadratic force contribution when paired with the actual quadratic vector. -/
theorem secondAxisTrace_partial_remainder_rotation_quadratic {parameters : PhaseParameters}
    (field coefficient : ACore parameters 3) (vanishes : ∀ direction, traceFirst direction field = 0)
    (outer inner direction first second : Fin 2) :
    secondAxisTrace first second (dotOperation parameters (partialCore parameters direction field)
      (rotationCore parameters (coordinateCore parameters outer (coordinateCore parameters inner coefficient)))) = 0 := by
  fin_cases outer <;> fin_cases inner
  all_goals simp [rotationCore,partialCore_coordinateCore,map_add,map_sub,
    dot_coordinate_second,traceZero_coordinateCore,
    secondAxisTrace_two_coordinates,traceZero_dot_zero_first,traceZero_partialCore,vanishes]

theorem secondAxisTrace_partial_quadratic_rotation_remainder {parameters : PhaseParameters}
    (field coefficient : ACore parameters 3) (vanishes : ∀ direction, traceFirst direction field = 0)
    (outer inner direction first second : Fin 2) :
    secondAxisTrace first second (dotOperation parameters
      (partialCore parameters direction (coordinateCore parameters outer (coordinateCore parameters inner coefficient)))
      (rotationCore parameters field)) = 0 := by
  fin_cases outer <;> fin_cases inner <;> fin_cases direction
  all_goals simp [rotationCore,partialCore_coordinateCore,map_add,map_sub,
    dot_coordinate_first,dot_coordinate_second,traceZero_coordinateCore,
    secondAxisTrace_two_coordinates,traceZero_dot_zero_second,traceZero_partialCore,vanishes]

end Grad.FinitePhysicalJetLift
