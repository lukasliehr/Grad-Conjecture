import GaugeTransferProof

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Constraints.Gauges.Consumer

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers Grad.Constraints.Gauges

/-- Immediate exact consumer chaining both accepted boundaries: the
written-order projection of any field lands in the source gauge kernels, its
literal N18 transfer lands in both target gauge kernels, and the reverse
transfer recovers it exactly; the seed-inverted outer radial component is
carried through unchanged at every closed polar point. -/
theorem projected_transfer_roundtrip (phase : PhaseParameters)
    (parameterM : Seed.Parameters) (insideM : parameterM ∈ Seed.parameterDomain)
    (parameterN : Seed.Parameters) (insideN : parameterN ∈ Seed.parameterDomain)
    (field : ACore phase 3) :
    poloidalCorrection phase parameterN insideN
        (seedTransfer phase parameterM insideM parameterN insideN
          (triangularGaugeProjection phase parameterM insideM field)) = 0 ∧
    toroidalCorrection phase parameterN insideN
        (seedTransfer phase parameterM insideM parameterN insideN
          (triangularGaugeProjection phase parameterM insideM field)) = 0 ∧
    seedTransfer phase parameterN insideN parameterM insideM
        (seedTransfer phase parameterM insideM parameterN insideN
          (triangularGaugeProjection phase parameterM insideM field)) =
      triangularGaugeProjection phase parameterM insideM field ∧
    ∀ (cell : ℤ) (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ),
      radialComponentAt angle (((seedInverseCore phase parameterN insideN
          (planarPartCore phase (seedTransfer phase parameterM insideM parameterN insideN
            (triangularGaugeProjection phase parameterM insideM field)))).1 cell).value
              (polarClosedPoint radius bounded angle)) =
        radialComponentAt angle (((seedInverseCore phase parameterM insideM
          (planarPartCore phase field)).1 cell).value
            (polarClosedPoint radius bounded angle)) := by
  obtain ⟨killsPoloidal, killsToroidal, _, _, _⟩ :=
    triangularGaugeProjection_algebra phase parameterM insideM
  refine ⟨seedTransfer_poloidal_gauge phase parameterM insideM parameterN insideN _,
    seedTransfer_toroidal_gauge phase parameterM insideM parameterN insideN _,
    seedTransfer_reverse phase parameterM insideM parameterN insideN _
      (killsPoloidal field) (killsToroidal field), ?_⟩
  intro cell radius bounded angle
  rw [seedTransfer_radial phase parameterM insideM parameterN insideN _ cell radius
    bounded angle]
  exact triangularGaugeProjection_radial_row phase parameterM insideM field cell radius
    bounded angle

/-- The ready form of the transfer block for downstream FA-COR27 and the
tame-derivative N5-transfer input. -/
theorem actualSeedTransfer_ready : SeedTransferGoal := actualSeedTransfer

end Grad.Constraints.Gauges.Consumer
