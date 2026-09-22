import AX7AxisBridge

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.AxisCore

open Grad.ClosedJets Grad.CartesianState
open Grad.ImplementationReadiness (statePack statePack_norm)
open Grad.SmoothingFamily (TGrade StateCore XAmbient stateToGrade)

/-- The exact ambient sum norm at both product nodes. -/
theorem xAmbient_norm (parameters : PhaseParameters) (grade : ℕ)
    (ambient : XAmbient parameters grade) :
    ‖ambient‖ =
      ‖ambient.ofLp.1‖ + ‖ambient.ofLp.2.ofLp.1‖ + ‖ambient.ofLp.2.ofLp.2‖ := by
  change ‖statePack ambient.ofLp.1 ambient.ofLp.2.ofLp.1 ambient.ofLp.2.ofLp.2‖ = _
  rw [statePack_norm]

/-- The embedded state norm is exactly the sum of the three embedded
component norms. -/
theorem stateToGrade_embedded_norm (parameters : PhaseParameters) (grade : ℕ)
    (state : StateCore parameters) :
    ‖stateToGrade parameters grade state‖ =
      ‖Grad.SmoothingFamily.axisToGrade parameters.sigma0 (grade + 1) state.1‖ +
        ‖aGradeEta (grade := grade) parameters (GradeCore.ofCoreLinear state.2.1)‖ +
          ‖aGradeEta (grade := grade) parameters (GradeCore.ofCoreLinear state.2.2)‖ := by
  change ‖statePack _ _ _‖ = _
  rw [statePack_norm]

/-- The grade-`q` state embedding has dense range: axis density from the
accepted finite-support core density, field densities from the accepted
completion embeddings. -/
theorem stateToGrade_denseRange (parameters : PhaseParameters) (grade : ℕ) :
    DenseRange (stateToGrade parameters grade) := by
  rw [Metric.denseRange_iff]
  intro ambient epsilon positive
  have third : 0 < epsilon / 3 := by linarith
  obtain ⟨axisCore, -, axisClose⟩ := axis_finite_support_dense parameters 2 (grade + 1)
    ambient.ofLp.1 (epsilon / 3) third
  obtain ⟨vectorGrade, vectorClose⟩ := Metric.denseRange_iff.mp
    (aGradeEta_denseRange (dimension := 3) (grade := grade) parameters)
    ambient.ofLp.2.ofLp.1 (epsilon / 3) third
  obtain ⟨scalarGrade, scalarClose⟩ := Metric.denseRange_iff.mp
    (aGradeEta_denseRange (dimension := 1) (grade := grade) parameters)
    ambient.ofLp.2.ofLp.2 (epsilon / 3) third
  refine ⟨(bridgeCore parameters axisCore, vectorGrade.toCore, scalarGrade.toCore), ?_⟩
  rw [dist_eq_norm] at vectorClose scalarClose ⊢
  have decompose : ‖ambient - stateToGrade parameters grade
      (bridgeCore parameters axisCore, vectorGrade.toCore, scalarGrade.toCore)‖ =
      ‖ambient.ofLp.1 - axisEta parameters 2 (grade + 1) axisCore‖ +
        ‖ambient.ofLp.2.ofLp.1 - aGradeEta parameters vectorGrade‖ +
          ‖ambient.ofLp.2.ofLp.2 - aGradeEta parameters scalarGrade‖ := by
    change ‖statePack (ambient.ofLp.1 - axisEta parameters 2 (grade + 1) axisCore)
      (ambient.ofLp.2.ofLp.1 - aGradeEta parameters vectorGrade)
      (ambient.ofLp.2.ofLp.2 - aGradeEta parameters scalarGrade)‖ = _
    rw [statePack_norm]
  rw [decompose]
  linarith

end Grad.AxisCore
