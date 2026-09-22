import BT20Completion

noncomputable section

namespace Grad.BoundaryTrace

open Grad.ClosedJets Grad.CartesianState

/-- The consumer is the actual original completion with the exact N20 half-order sequence target. -/
def CompletedBoundaryTraceGoal : Prop :=
  ∀ grade : ℕ, 1 ≤ grade → ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ dimension (parameters : PhaseParameters),
      ∃ trace : AGrade parameters dimension grade →L[ℂ]
          BoundaryGrade parameters (ComplexEuclidean dimension) grade,
        ‖trace‖ ≤ constant ∧
        ∀ field : GradeCore parameters dimension grade, ∀ mode : ℤ × ℤ,
          boundaryCoefficient parameters grade (trace (aGradeEta parameters field)) mode =
            originalBoundaryCoefficient parameters field.toCore mode

def BlockGoal : Prop := BoundaryTraceGoal ∧ CompletedBoundaryTraceGoal

end Grad.BoundaryTrace
