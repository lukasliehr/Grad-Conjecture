import AX10AmbientProof

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.AxisCore.Consumer

open Grad.ClosedJets Grad.CartesianState Grad.AxisCore
open Grad.SmoothingFamily (TGrade StateCore XAmbient stateToGrade)

/-- Immediate exact consumer: every grade-`q` ambient element (`q ≥ 3`) is
`epsilon`-approximated by an embedded smooth state whose ambient norm is
exactly the sum of its three embedded component norms. -/
theorem ambient_state_approximation (parameters : PhaseParameters) (grade : ℕ)
    (atLeastThree : 3 ≤ grade) (ambient : XAmbient parameters grade)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ state : StateCore parameters,
      ‖ambient - stateToGrade parameters grade state‖ < epsilon ∧
      ‖stateToGrade parameters grade state‖ =
        ‖Grad.SmoothingFamily.axisToGrade parameters.sigma0 (grade + 1) state.1‖ +
          ‖aGradeEta (grade := grade) parameters (GradeCore.ofCoreLinear state.2.1)‖ +
            ‖aGradeEta (grade := grade) parameters (GradeCore.ofCoreLinear state.2.2)‖ := by
  obtain ⟨-, isometry, -, dense⟩ := actualAmbientProduct parameters grade atLeastThree
  obtain ⟨state, close⟩ := Metric.denseRange_iff.mp dense ambient epsilon positive
  rw [dist_eq_norm] at close
  exact ⟨state, close, isometry state⟩

/-- The literal grade-three instantiation of the accepted goal. -/
theorem ambient_ready_three (parameters : PhaseParameters) :
    (∀ ambient : XAmbient parameters 3,
      ‖ambient‖ =
        ‖ambient.ofLp.1‖ + ‖ambient.ofLp.2.ofLp.1‖ + ‖ambient.ofLp.2.ofLp.2‖) ∧
    (∀ state : StateCore parameters,
      ‖stateToGrade parameters 3 state‖ =
        ‖Grad.SmoothingFamily.axisToGrade parameters.sigma0 4 state.1‖ +
          ‖aGradeEta (grade := 3) parameters (GradeCore.ofCoreLinear state.2.1)‖ +
            ‖aGradeEta (grade := 3) parameters (GradeCore.ofCoreLinear state.2.2)‖) ∧
    Function.Injective (stateToGrade parameters 3) ∧
    DenseRange (stateToGrade parameters 3) :=
  actualAmbientProduct parameters 3 le_rfl

end Grad.AxisCore.Consumer
