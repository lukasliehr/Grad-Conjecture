import CP13Goal

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Cor18

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.Constraints.Gauges Grad.Constraints.Multipliers Grad.BoundaryTrace Grad.BoundaryLift
open Grad.SmoothingFamily Grad.ImplementationReadiness Grad.AxisCore

/-! Immediate exact consumers of the COR18 goal, through the goal statement
alone: every projected state satisfies the full constraint kernel, every
constrained state is fixed, and the grade-three bound on the literal COR17
product norm. -/

/-- Every projected state lies in the full constraint kernel. -/
theorem projected_state_constrained (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain) :
    ∃ projection : StateCore parameters →ₗ[ℂ] StateCore parameters,
      ∀ state : StateCore parameters,
        (∀ cell : ℤ, ZeroCartesianFirstJets ((projection state).2.1.1 cell)) ∧
        poloidalCorrection parameters parameter inside (projection state).2.1 = 0 ∧
        toroidalCorrection parameters parameter inside (projection state).2.1 = 0 ∧
        physicalRow parameters parameter inside (projection state).2.1 = 0 ∧
        angularCore parameters 0 (projection state).2.2 = 0 := by
  obtain ⟨projection, _, _, _, range⟩ := actualFullProjection parameters parameter inside
  exact ⟨projection, fun state => (range (projection state)).mp ⟨state, rfl⟩⟩

/-- Every state in the full constraint kernel is fixed by the projection. -/
theorem constrained_state_fixed (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain) :
    ∃ projection : StateCore parameters →ₗ[ℂ] StateCore parameters,
      ∀ state : StateCore parameters,
        (∀ cell : ℤ, ZeroCartesianFirstJets (state.2.1.1 cell)) →
        poloidalCorrection parameters parameter inside state.2.1 = 0 →
        toroidalCorrection parameters parameter inside state.2.1 = 0 →
        physicalRow parameters parameter inside state.2.1 = 0 →
        angularCore parameters 0 state.2.2 = 0 →
        projection state = state := by
  obtain ⟨projection, _, _, idempotent, range⟩ := actualFullProjection parameters parameter inside
  refine ⟨projection, fun state jets poloidal toroidal row mean => ?_⟩
  obtain ⟨source, sourceLaw⟩ := (range state).mpr ⟨jets, poloidal, toroidal, row, mean⟩
  rw [← sourceLaw, idempotent source]

/-- The grade-three instance of the same-grade bound. -/
theorem projection_grade_three_bound (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain) :
    ∃ projection : StateCore parameters →ₗ[ℂ] StateCore parameters, ∃ constant : ℝ,
      0 ≤ constant ∧ ∀ state : StateCore parameters,
        ‖stateToGrade parameters 3 (projection state)‖ ≤
          constant * ‖stateToGrade parameters 3 state‖ := by
  obtain ⟨projection, _, bounds, _, _⟩ := actualFullProjection parameters parameter inside
  obtain ⟨constant, nonneg, bound⟩ := bounds 3 le_rfl
  exact ⟨projection, constant, nonneg, bound⟩

end Grad.Cor18
