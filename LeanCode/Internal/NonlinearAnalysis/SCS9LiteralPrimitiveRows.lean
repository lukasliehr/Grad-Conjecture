import SCS8G3AngularRows

noncomputable section
open Set MeasureTheory

namespace Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.BoundaryTrace

/-- The exact completed division realization at any admitted input grade.
Only the original value-flat condition is used. -/
theorem dividedRow_flat_literal {dimension grade power : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power + 3 ≤ grade)
    (field : AGrade parameters dimension grade)
    (flat : OriginalValueFlat parameters (by omega) field) (mode : ℤ × ℤ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1,
      completedDivisionRow (power := power) (radial := 0) lower positive bounded parameters paid field mode radius =
        ((annularFrequency mode.1 mode.2 : ℂ) ^ power) • (Real.sqrt radius •
          angularCoefficient (fun angle =>
            cartesianWeight parameters mode.2 (polarPlane (radius, angle)) •
              (radius⁻¹ • completedOriginalCell parameters (by omega) mode.2 field
                (polarClosedPoint radius angle (positive.le.trans inside.1) inside.2))) mode.1) := by
  rw [completedDivisionRow_literal]
  filter_upwards [Lp.coeFn_smul ((annularFrequency mode.1 mode.2 : ℂ) ^ power)
      (continuousDifferenceLp lower positive bounded mode.1
        (completedWeightedCell parameters (by omega) mode.2 field)),
    radialToLp_ae lower
      (continuousDifferenceCoefficient lower positive bounded mode.1
        (completedWeightedCell parameters (by omega) mode.2 field))
      (continuousDifferenceCoefficient_continuous lower positive bounded mode.1
        (completedWeightedCell parameters (by omega) mode.2 field))]
    with radius scaling representative
  intro inside
  change continuousDifferenceLp lower positive bounded mode.1
    (completedWeightedCell parameters (by omega) mode.2 field) radius = _ at representative
  rw [scaling, Pi.smul_apply, representative]
  congr 2
  unfold continuousDifferenceCoefficient
  congr 1
  funext angle
  exact continuousDifferenceQuotient_flat lower positive bounded parameters (by omega) field flat
    mode.2 radius inside angle

theorem restrictedRow_literal {dimension grade power : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power ≤ grade) (large : 3 ≤ grade)
    (field : AGrade parameters dimension grade) (mode : ℤ × ℤ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1,
      completedRestrictionRow (power := power) (radial := 0) lower positive bounded parameters (by omega) field mode radius =
        ((annularFrequency mode.1 mode.2 : ℂ) ^ power) • (Real.sqrt radius •
          angularCoefficient (fun angle =>
            cartesianWeight parameters mode.2 (polarPlane (radius, angle)) •
              completedOriginalCell parameters large mode.2 field
                (polarClosedPoint radius angle (positive.le.trans inside.1) inside.2)) mode.1) := by
  rw [completedRestrictionRow_literal lower positive bounded parameters (by omega) large]
  filter_upwards [Lp.coeFn_smul ((annularFrequency mode.1 mode.2 : ℂ) ^ power)
      (continuousPolarLp lower positive bounded mode.1 (completedWeightedCell parameters large mode.2 field)),
    radialToLp_ae lower
      (continuousPolarCoefficient lower positive bounded mode.1 (completedWeightedCell parameters large mode.2 field))
      (continuousPolarCoefficient_continuous lower positive bounded mode.1 (completedWeightedCell parameters large mode.2 field))]
    with radius scaling representative
  intro inside
  change continuousPolarLp lower positive bounded mode.1 (completedWeightedCell parameters large mode.2 field) radius = _ at representative
  rw [scaling, Pi.smul_apply, representative]
  congr 2
  unfold continuousPolarCoefficient
  congr 1
  funext angle
  exact continuousPolarValue_completed lower positive bounded parameters large field mode.2 radius inside angle

end Grad.SourceCollarFullSource
