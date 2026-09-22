import AKU35OriginalPolynomialCoordinateDecomposition

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct

theorem traceZero_originalProduct_zero_slot {parameters : PhaseParameters} {arity outputDimension : ℕ}
    {dimensions : Fin (arity+1) → ℕ}
    (multiplication : ContinuousMultilinearMap ℂ
      (fun index => ComplexEuclidean (dimensions index)) (ComplexEuclidean outputDimension))
    (fields : (index : Fin (arity+1)) → ACore parameters (dimensions index))
    (slot : Fin (arity+1)) (vanishes : traceZero (fields slot) = 0) :
    traceZero (actualMultilinearProduct parameters multiplication fields) = 0 := by
  apply Subtype.ext
  funext cell
  rw [traceZero_val]
  change ((actualMultilinearProduct parameters multiplication fields).val cell).value originPoint = 0
  rw [actualMultilinearProduct_isActual]
  unfold productCoefficientValue
  have zeroTerms (assignment : CellAssignments (arity+1) cell) :
      multiplication (fun index => ((fields index).val (assignment.val index)).value originPoint) = 0 := by
    apply multiplication.map_coord_zero (i := slot)
    exact congrArg (fun axis : Grad.AxisCore.AxisSmoothCore parameters (dimensions slot) =>
      axis.val (assignment.val slot)) vanishes
  simp only [zeroTerms,tsum_zero]

theorem traceZero_dot_zero_first {parameters : PhaseParameters}
    (first second : ACore parameters 3) (vanishes : traceZero first = 0) :
    traceZero (dotOperation parameters first second) = 0 :=
  traceZero_originalProduct_zero_slot physicalDotProduct ![first,second] 0 vanishes

theorem traceZero_dot_zero_second {parameters : PhaseParameters}
    (first second : ACore parameters 3) (vanishes : traceZero second = 0) :
    traceZero (dotOperation parameters first second) = 0 :=
  traceZero_originalProduct_zero_slot physicalDotProduct ![first,second] 1 vanishes

/-- The exact original first Taylor field, including every cell frequency. -/
def originalLinearTaylorCore {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) : ACore parameters dimension :=
  coordinateCore parameters 0 (axisConstantCore (traceFirst 0 field)) +
    coordinateCore parameters 1 (axisConstantCore (traceFirst 1 field))

theorem originalLinearTaylorCore_first {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (direction : Fin 2) :
    traceFirst direction (originalLinearTaylorCore field) = traceFirst direction field := by
  rw [originalLinearTaylorCore,map_add,traceFirst_coordinateCore,traceFirst_coordinateCore,
    traceZero_axisConstantCore,traceZero_axisConstantCore]
  fin_cases direction <;> simp

theorem originalLinearTaylorCore_remainder_first {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (direction : Fin 2) :
    traceFirst direction (field-originalLinearTaylorCore field) = 0 := by
  rw [map_sub,originalLinearTaylorCore_first,sub_self]

end Grad.FinitePhysicalJetLift
