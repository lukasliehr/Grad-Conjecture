import BLInterface
import BL44AngularOperators

noncomputable section

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

/-- The actual same-grade boundary coretraction: one complex-linear
smooth-core operator chosen before the grade, with all q>=1 original
A bounds, the literal double-Fourier exponential kernel, the actual
original boundary coefficient right inverse, reality, zero near the
axis, high-angular support, and the completed right inverse to the
accepted completed trace. -/
theorem boundaryLiftTheorem : BoundaryLiftGoal := by
  intro parameters
  refine ⟨fun grade => Real.sqrt (originalLiftCellConstant parameters grade),
    fun grade => Real.sqrt_nonneg _, ?_⟩
  intro dimension
  refine ⟨boundaryLift parameters, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro grade gradePositive values
    exact boundaryLift_norm_le parameters grade gradePositive values
  · intro values mode
    exact boundaryLift_coefficient parameters values mode
  · intro values point inside cell
    exact boundaryLift_zero_inner parameters values cell point inside
  · intro values point time timeNonneg timeLe angle cell pointLaw
    exact boundaryLift_physical_value parameters values point time timeNonneg timeLe
      angle cell pointLaw
  · intro values reality cell
    exact boundaryLift_reality parameters values reality cell
  · intro values highSupport mode modeSmall cell
    exact boundaryLift_high_support parameters values highSupport mode modeSmall cell
  · intro grade gradePositive
    refine ⟨completedBoundaryLift parameters grade gradePositive,
      completedBoundaryLift_norm_le parameters grade gradePositive,
      completedBoundaryLift_trace parameters grade gradePositive, ?_⟩
    intro values
    exact (boundaryLift_component parameters grade gradePositive values).symm

/-- Literal N28 boundary multiplication under the exact N6 coefficient
envelope, on the actual fixed half-order completed target. -/
theorem boundaryMultiplicationTheorem : BoundaryMultiplicationGoal := by
  intro grade _gradePositive parameters sourceDimension targetDimension coefficients
    envelopeSummable
  exact ⟨boundaryMultiplication parameters grade coefficients,
    boundaryMultiplication_norm_le parameters grade coefficients envelopeSummable,
    fun field mode => boundaryMultiplication_coefficient_hasSum parameters grade coefficients
      envelopeSummable field mode⟩

/-- The exact angular shifts and the five-mode complement projection on
every boundary grade. -/
theorem boundaryAngularOperationsTheorem : BoundaryAngularOperationsGoal := by
  intro grade _gradePositive parameters dimension
  constructor
  · intro shift
    exact ⟨angularShiftOperator parameters grade dimension shift,
      angularShiftOperator_norm_le parameters grade dimension shift,
      fun field mode => angularShiftOperator_coefficient parameters grade dimension shift
        field mode⟩
  · exact ⟨highComplementProjection parameters grade dimension,
      highComplementProjection_norm_le parameters grade dimension,
      highComplementProjection_idempotent parameters grade dimension,
      fun field mode => highComplementProjection_coefficient parameters grade dimension
        field mode⟩

/-- The complete FA-constraints-boundary-lift public block. -/
theorem boundaryLiftBlock : BlockGoal :=
  ⟨boundaryLiftTheorem, boundaryMultiplicationTheorem, boundaryAngularOperationsTheorem⟩

end Grad.BoundaryLift
