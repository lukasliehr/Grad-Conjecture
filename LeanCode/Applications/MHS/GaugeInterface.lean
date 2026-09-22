import GaugeRadialRow

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers

/-- The exact FA-constraints-gauges N12–N15 public goal.  The two corrections
are pinned to the literal written N12 formulas built from the accepted seed
multipliers, the accepted N3 tangential projection, the accepted N1 toroidal
mean and the actual Cartesian `u · M' y` multiplication; the ordered
`Q_g = (I - C_t)(I - C_p)` must be a bounded same-grade projection onto the
intersection of the two gauge kernels, preserve zero first Cartesian jets and
leave the seed-inverted outer radial row literally unchanged at every closed
polar point. -/
def GaugesGoal : Prop :=
  ∀ (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain),
    ∃ poloidal toroidal : ACore phase 3 →ₗ[ℂ] ACore phase 3,
      (∀ field, poloidal field =
        planarInclusionCore phase (seedMatrixCore phase parameter inside
          (tangentialCore phase (seedTransposeCore phase parameter inside
            (planarPartCore phase field))))) ∧
      (∀ field, toroidal field =
        toroidalInclusionCore phase (angularCore phase 0
          (toroidalPartCore phase field +
            (phase.length⁻¹ : ℂ) • derivativeDotCore phase parameter inside
              (planarPartCore phase field)))) ∧
      (∀ field cell point,
        ((derivativeDotCore phase parameter inside field).1 cell).value point =
          point.val 0 • ∑' shift, derivativeRowCoefficients parameter 0 shift
              ((field.1 (cell - shift)).value point) +
            point.val 1 • ∑' shift, derivativeRowCoefficients parameter 1 shift
              ((field.1 (cell - shift)).value point)) ∧
      (∃ constants : ℕ → ℝ, (∀ grade, 0 ≤ constants grade) ∧
        ∀ (grade : ℕ) field,
          ‖GradeCore.ofCoreLinear (grade := grade)
              (triangularProjection poloidal toroidal field)‖ ≤
            constants grade * ‖GradeCore.ofCoreLinear (grade := grade) field‖) ∧
      (∀ field, poloidal (poloidal field) = poloidal field) ∧
      (∀ field, toroidal (toroidal field) = toroidal field) ∧
      (∀ field, poloidal (toroidal field) = 0) ∧
      (∀ field, triangularProjection poloidal toroidal
          (triangularProjection poloidal toroidal field) =
        triangularProjection poloidal toroidal field) ∧
      (LinearMap.range (triangularProjection poloidal toroidal) =
        LinearMap.ker poloidal ⊓ LinearMap.ker toroidal) ∧
      (∀ field, (∀ cell, ZeroCartesianFirstJets (field.1 cell)) →
        ∀ cell, ZeroCartesianFirstJets
          ((triangularProjection poloidal toroidal field).1 cell)) ∧
      (∀ field (cell : ℤ) (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ),
        radialComponentAt angle (((seedInverseCore phase parameter inside
            (planarPartCore phase (triangularProjection poloidal toroidal field))).1
              cell).value (polarClosedPoint radius bounded angle)) =
          radialComponentAt angle (((seedInverseCore phase parameter inside
            (planarPartCore phase field)).1 cell).value
              (polarClosedPoint radius bounded angle)))

end Grad.Constraints.Gauges
