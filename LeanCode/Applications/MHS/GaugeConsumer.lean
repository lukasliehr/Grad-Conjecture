import GaugeProof

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Constraints.Gauges.Consumer

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers Grad.Constraints.Gauges

/-- Immediate exact consumer: the written-order projection of every original
field is an explicit representative inside both actual seed gauge kernels;
it preserves zero first Cartesian jets, and its seed-inverted outer radial
component agrees literally with that of the original field at every closed
polar point. -/
theorem gaugeFixed_representative (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore phase 3) :
    poloidalCorrection phase parameter inside
        (triangularGaugeProjection phase parameter inside field) = 0 ∧
    toroidalCorrection phase parameter inside
        (triangularGaugeProjection phase parameter inside field) = 0 ∧
    ((∀ cell, ZeroCartesianFirstJets (field.1 cell)) →
      ∀ cell, ZeroCartesianFirstJets
        ((triangularGaugeProjection phase parameter inside field).1 cell)) ∧
    ∀ (cell : ℤ) (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ),
      radialComponentAt angle (((seedInverseCore phase parameter inside
          (planarPartCore phase (triangularGaugeProjection phase parameter inside field))).1
            cell).value (polarClosedPoint radius bounded angle)) =
        radialComponentAt angle (((seedInverseCore phase parameter inside
          (planarPartCore phase field)).1 cell).value
            (polarClosedPoint radius bounded angle)) := by
  obtain ⟨killsPoloidal, killsToroidal, _, _, _⟩ :=
    triangularGaugeProjection_algebra phase parameter inside
  exact ⟨killsPoloidal field, killsToroidal field,
    fun zeroJets => triangularGaugeProjection_zero_first_jets phase parameter inside
      field zeroJets,
    fun cell radius bounded angle => triangularGaugeProjection_radial_row phase parameter
      inside field cell radius bounded angle⟩

/-- Immediate exact consumer: the projection is same-grade bounded with the
explicit written constant, and acts as the identity precisely on the
intersection of the two gauge kernels. -/
theorem gaugeFixed_subspace (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) :
    (∀ (grade : ℕ) (field : ACore phase 3),
      ‖GradeCore.ofCoreLinear (grade := grade)
          (triangularGaugeProjection phase parameter inside field)‖ ≤
        triangularGradeConstant phase parameter grade *
          ‖GradeCore.ofCoreLinear (grade := grade) field‖) ∧
    LinearMap.range (triangularGaugeProjection phase parameter inside) =
      LinearMap.ker (poloidalCorrection phase parameter inside) ⊓
        LinearMap.ker (toroidalCorrection phase parameter inside) := by
  obtain ⟨_, _, _, _, rangeLaw⟩ := triangularGaugeProjection_algebra phase parameter inside
  refine ⟨?_, rangeLaw⟩
  intro grade field
  rw [ofCoreLinear_norm_coordinates, ofCoreLinear_norm_coordinates]
  exact triangularGaugeProjection_coordinates_bound phase parameter inside field

/-- The ready form of the public block for downstream N16–N19 and COR18 use. -/
theorem actualGauges_ready : GaugesGoal := actualGauges

end Grad.Constraints.Gauges.Consumer
