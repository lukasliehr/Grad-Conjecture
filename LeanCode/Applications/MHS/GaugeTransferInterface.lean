import GaugeSliceBounds

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers

/-- The exact N16–N19 seed-slice transfer goal: one literal N18 family over
all pairs of actual admissible seeds, with the written planar and tangential
formulas, both target gauges killed, same-grade bounds, zero first jets,
the exact N19 seed-inverted outer radial law, the exact reverse inverse on
the source gauge kernels, the identity law and the three-seed cocycle. -/
def SeedTransferGoal : Prop :=
  ∀ phase : PhaseParameters,
    ∃ transfer : ∀ parameterM : Seed.Parameters, parameterM ∈ Seed.parameterDomain →
        ∀ parameterN : Seed.Parameters, parameterN ∈ Seed.parameterDomain →
        (ACore phase 3 →ₗ[ℂ] ACore phase 3),
      (∀ (parameterM : Seed.Parameters) (insideM : parameterM ∈ Seed.parameterDomain)
        (parameterN : Seed.Parameters) (insideN : parameterN ∈ Seed.parameterDomain),
        (∀ field, planarPartCore phase
            (transfer parameterM insideM parameterN insideN field) =
          seedMatrixCore phase parameterN insideN (sliceProjection phase parameterN insideN
            (seedInverseCore phase parameterM insideM (planarPartCore phase field)))) ∧
        (∀ field, toroidalPartCore phase
            (transfer parameterM insideM parameterN insideN field) =
          (toroidalPartCore phase field -
            angularCore phase 0 (toroidalPartCore phase field)) -
            (phase.length⁻¹ : ℂ) • angularCore phase 0 (derivativeDotCore phase parameterN
              insideN (planarPartCore phase
                (transfer parameterM insideM parameterN insideN field)))) ∧
        (∀ field, poloidalCorrection phase parameterN insideN
            (transfer parameterM insideM parameterN insideN field) = 0) ∧
        (∀ field, toroidalCorrection phase parameterN insideN
            (transfer parameterM insideM parameterN insideN field) = 0) ∧
        (∃ constants : ℕ → ℝ, (∀ grade, 0 ≤ constants grade) ∧
          ∀ (grade : ℕ) field,
            ‖GradeCore.ofCoreLinear (grade := grade)
                (transfer parameterM insideM parameterN insideN field)‖ ≤
              constants grade * ‖GradeCore.ofCoreLinear (grade := grade) field‖) ∧
        (∀ field, (∀ cell, ZeroCartesianFirstJets (field.1 cell)) →
          ∀ cell, ZeroCartesianFirstJets
            ((transfer parameterM insideM parameterN insideN field).1 cell)) ∧
        (∀ field (cell : ℤ) (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ),
          radialComponentAt angle (((seedInverseCore phase parameterN insideN
              (planarPartCore phase (transfer parameterM insideM parameterN insideN
                field))).1 cell).value (polarClosedPoint radius bounded angle)) =
            radialComponentAt angle (((seedInverseCore phase parameterM insideM
              (planarPartCore phase field)).1 cell).value
                (polarClosedPoint radius bounded angle)))) ∧
      (∀ (parameterM : Seed.Parameters) (insideM : parameterM ∈ Seed.parameterDomain)
        (parameterN : Seed.Parameters) (insideN : parameterN ∈ Seed.parameterDomain) field,
        poloidalCorrection phase parameterM insideM field = 0 →
        toroidalCorrection phase parameterM insideM field = 0 →
        transfer parameterN insideN parameterM insideM
          (transfer parameterM insideM parameterN insideN field) = field) ∧
      (∀ (parameterM : Seed.Parameters) (insideM : parameterM ∈ Seed.parameterDomain)
        (parameterN : Seed.Parameters) (insideN : parameterN ∈ Seed.parameterDomain)
        (parameterP : Seed.Parameters) (insideP : parameterP ∈ Seed.parameterDomain) field,
        transfer parameterN insideN parameterP insideP
            (transfer parameterM insideM parameterN insideN field) =
          transfer parameterM insideM parameterP insideP field) ∧
      (∀ (parameterM : Seed.Parameters) (insideM : parameterM ∈ Seed.parameterDomain) field,
        poloidalCorrection phase parameterM insideM field = 0 →
        toroidalCorrection phase parameterM insideM field = 0 →
        transfer parameterM insideM parameterM insideM field = field)

end Grad.Constraints.Gauges
