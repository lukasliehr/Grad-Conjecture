import AX8AmbientDensity

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.AxisCore

open Grad.ClosedJets Grad.CartesianState
open Grad.SmoothingFamily (TGrade StateCore XAmbient stateToGrade)

/-- The exact COR17 goal at every grade at least three: the literal
completed Cartesian product `XAmbient` with the exact sum norm at both
product nodes, and the grade-`q` linear injective isometric dense embedding
of the one all-grade smooth product. -/
def AmbientProductGoal : Prop :=
  ∀ (parameters : PhaseParameters) (grade : ℕ), 3 ≤ grade →
    (∀ ambient : XAmbient parameters grade,
      ‖ambient‖ =
        ‖ambient.ofLp.1‖ + ‖ambient.ofLp.2.ofLp.1‖ + ‖ambient.ofLp.2.ofLp.2‖) ∧
    (∀ state : StateCore parameters,
      ‖stateToGrade parameters grade state‖ =
        ‖Grad.SmoothingFamily.axisToGrade parameters.sigma0 (grade + 1) state.1‖ +
          ‖aGradeEta (grade := grade) parameters (GradeCore.ofCoreLinear state.2.1)‖ +
            ‖aGradeEta (grade := grade) parameters (GradeCore.ofCoreLinear state.2.2)‖) ∧
    Function.Injective (stateToGrade parameters grade) ∧
    DenseRange (stateToGrade parameters grade)

end Grad.AxisCore
