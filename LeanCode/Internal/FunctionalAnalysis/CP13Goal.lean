import CP12FullProjection

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Cor18

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.Constraints.Gauges Grad.Constraints.Multipliers Grad.BoundaryTrace Grad.BoundaryLift
open Grad.SmoothingFamily Grad.ImplementationReadiness Grad.AxisCore

/-! # The exact COR18 goal

For every actual admissible N10 seed, one linear projection on the accepted
smooth full product `StateCore` (COR17's carrier), literally
`P_M(τ, u, s) = (τ, (I - C_{∂,M} B_M)(I - C_t)(I - C_p) Q_A u, (I - Π) s)`
with the accepted `Q_A`, `(I - C_t)(I - C_p)`, the literal N29 row `B_M` and
collar correction `C_{∂,M}` of this lane, and the accepted angular mean `Π`:
bounded at every grade `q ≥ 3` in the literal COR17 product norm,
idempotent, with exact range — free axis coordinate, vector zero first jet,
both N gauges and the N29 physical outer slice, mean-zero scalar. The
projection is an output; nothing is assumed about it. -/

def FullProjectionGoal : Prop :=
  ∀ (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain),
    ∃ projection : StateCore parameters →ₗ[ℂ] StateCore parameters,
      (∀ state : StateCore parameters, projection state =
        (state.1, outerCorrection parameters parameter inside
          (triangularGaugeProjection parameters parameter inside (axisJetProjection state.2.1)),
          state.2.2 - angularCore parameters 0 state.2.2)) ∧
      (∀ grade : ℕ, 3 ≤ grade → ∃ constant : ℝ, 0 ≤ constant ∧
        ∀ state : StateCore parameters,
          ‖stateToGrade parameters grade (projection state)‖ ≤
            constant * ‖stateToGrade parameters grade state‖) ∧
      (∀ state : StateCore parameters, projection (projection state) = projection state) ∧
      (∀ state : StateCore parameters,
        (∃ source : StateCore parameters, projection source = state) ↔
          ((∀ cell : ℤ, ZeroCartesianFirstJets (state.2.1.1 cell)) ∧
            poloidalCorrection parameters parameter inside state.2.1 = 0 ∧
            toroidalCorrection parameters parameter inside state.2.1 = 0 ∧
            physicalRow parameters parameter inside state.2.1 = 0 ∧
            angularCore parameters 0 state.2.2 = 0))

/-- COR18: the full-domain projection goal holds. -/
theorem actualFullProjection : FullProjectionGoal := by
  intro parameters parameter inside
  refine ⟨fullProjection parameters parameter inside, fun state => ?_,
    fullProjection_norm_le parameters parameter inside,
    fullProjection_idempotent parameters parameter inside, fun state => ?_⟩
  · rw [fullProjection_apply, vectorProjection_apply]
  · rw [fullProjection_range_iff]
    exact ⟨fun ⟨⟨jets, poloidal, toroidal, row⟩, mean⟩ => ⟨jets, poloidal, toroidal, row, mean⟩,
      fun ⟨jets, poloidal, toroidal, row, mean⟩ => ⟨⟨jets, poloidal, toroidal, row⟩, mean⟩⟩

end Grad.Cor18
