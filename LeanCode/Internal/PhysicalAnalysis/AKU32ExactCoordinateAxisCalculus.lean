import AKU30OriginalLiftAxisJetsAndSupport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearDivision

/-- Exact original-core product rule for a Cartesian coordinate factor. -/
theorem partialCore_coordinateCore {parameters : PhaseParameters} {dimension : ℕ}
    (direction coordinate : Fin 2) (field : ACore parameters dimension) :
    partialCore parameters direction (coordinateCore parameters coordinate field) =
      (if direction = coordinate then field else 0) +
        coordinateCore parameters coordinate (partialCore parameters direction field) := by
  apply Subtype.ext
  funext cell
  rw [partialCore_val,coordinateCore_val]
  change Grad.GaugeCoefficients.Physical.Compensated.partialJet direction (coordinateJet coordinate (field.val cell)) = _
  rw [partial_coordinateJet]
  fin_cases direction <;> fin_cases coordinate <;> simp [spatialBasis]
  all_goals rfl

theorem traceZero_coordinateCore {parameters : PhaseParameters} {dimension : ℕ}
    (coordinate : Fin 2) (field : ACore parameters dimension) :
    traceZero (coordinateCore parameters coordinate field) = 0 := by
  apply Subtype.ext
  funext cell
  rw [traceZero_val,coordinateCore_val,coordinateJet_originValue]
  rfl

/-- The true ordered second derivative, valued in the original all-grade
axis core. The order is never silently replaced by a symmetric symbol. -/
def secondAxisTrace {parameters : PhaseParameters} {dimension : ℕ}
    (first second : Fin 2) : ACore parameters dimension →ₗ[ℂ] Grad.AxisCore.AxisSmoothCore parameters dimension :=
  (traceFirst first).comp (partialCore parameters second)

theorem secondAxisTrace_coordinate {parameters : PhaseParameters} {dimension : ℕ}
    (first second coordinate : Fin 2) (field : ACore parameters dimension) :
    secondAxisTrace first second (coordinateCore parameters coordinate field) =
      (if second = coordinate then traceFirst first field else 0) +
        (if first = coordinate then traceFirst second field else 0) := by
  change traceFirst first (partialCore parameters second (coordinateCore parameters coordinate field)) = _
  rw [partialCore_coordinateCore,map_add,traceFirst_coordinateCore]
  have same : traceZero (partialCore parameters second field) = traceFirst second field := rfl
  rw [same]
  by_cases equality : second = coordinate <;> simp [equality]

theorem secondAxisTrace_two_coordinates {parameters : PhaseParameters} {dimension : ℕ}
    (first second outer inner : Fin 2) (field : ACore parameters dimension) :
    secondAxisTrace first second (coordinateCore parameters outer (coordinateCore parameters inner field)) =
      (if second = outer ∧ first = inner then traceZero field else 0) +
        (if first = outer ∧ second = inner then traceZero field else 0) := by
  rw [secondAxisTrace_coordinate,traceFirst_coordinateCore,traceFirst_coordinateCore]
  split_ifs <;> simp_all

theorem secondAxisTrace_three_coordinates {parameters : PhaseParameters} {dimension : ℕ}
    (first second outer middle inner : Fin 2) (field : ACore parameters dimension) :
    secondAxisTrace first second (coordinateCore parameters outer
      (coordinateCore parameters middle (coordinateCore parameters inner field))) = 0 := by
  rw [secondAxisTrace_two_coordinates,traceZero_coordinateCore]
  split_ifs <;> simp

/-- The genuine Taylor coefficient extraction for any vector dimension. -/
def secondTaylorAxis {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) : Fin 3 → Grad.AxisCore.AxisSmoothCore parameters dimension :=
  ![(1/2 : ℂ) • secondAxisTrace 0 0 field,secondAxisTrace 0 1 field,
    (1/2 : ℂ) • secondAxisTrace 1 1 field]

theorem secondTaylorAxis_two_coordinates {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (index : Fin 3) :
    secondTaylorAxis
      (![coordinateCore parameters 0 (coordinateCore parameters 0 field),
        coordinateCore parameters 0 (coordinateCore parameters 1 field),
        coordinateCore parameters 1 (coordinateCore parameters 1 field)] index) =
      Pi.single index (traceZero field) := by
  funext slot
  fin_cases index <;> fin_cases slot <;>
    simp [secondTaylorAxis,secondAxisTrace_two_coordinates]
  all_goals module

theorem secondTaylorAxis_three_coordinates {parameters : PhaseParameters} {dimension : ℕ}
    (outer middle inner : Fin 2) (field : ACore parameters dimension) :
    secondTaylorAxis (coordinateCore parameters outer
      (coordinateCore parameters middle (coordinateCore parameters inner field))) = 0 := by
  funext index
  fin_cases index <;> simp [secondTaylorAxis,secondAxisTrace_three_coordinates]

end Grad.FinitePhysicalJetLift
