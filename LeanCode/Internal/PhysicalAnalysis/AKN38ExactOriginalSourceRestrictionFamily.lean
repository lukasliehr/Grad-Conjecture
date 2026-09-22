import AKN34ExactOriginalSourceFamily
import AKN37ActualFullG3Restriction

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.SourceCollarFullSource Grad.SourceCollarCoefficients Grad.AnnularCurrentSource
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.ConstrainedGrades
open Grad.SourceCollarBulk Grad.AnnularStrongData Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularRestriction Grad.SourceCollarAngular

/-- Literal original four-block source restriction. Both AH derivative
coordinates follow from their actual graph representatives; G3 includes its
entire angular strengthening and its original circle correction. -/
theorem actualOriginalSourceDatum_restrict (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (lower upper : ℝ) (included : lower ≤ upper) (positiveLower : 0 < lower) (positiveUpper : 0 < upper)
    (boundedLower : lower < 1) (boundedUpper : upper < 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (flat : IsFlat source) :
    originalFullSourceRestriction parameters lower upper included
      (actualOriginalSourceDatum parameters L rho epsilon field small lower positiveLower boundedLower grade source flat).val.ofLp.1 =
    (actualOriginalSourceDatum parameters L rho epsilon field small upper positiveUpper boundedUpper grade source flat).val.ofLp.1 := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
  apply Prod.ext
  · apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
    exact Prod.ext
      (actualOriginalF0Graph_restrict parameters lower upper included positiveLower positiveUpper boundedLower boundedUpper grade source)
      (actualOriginalF2Graph_restrict parameters L lower upper included positiveLower positiveUpper boundedLower boundedUpper grade source)
  · apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
    exact Prod.ext
      (actualOriginalF1Row_restrict parameters lower upper included positiveLower positiveUpper boundedLower.le boundedUpper.le grade source)
      (actualOriginalG3Row_restrict parameters L rho epsilon field small lower upper included positiveLower positiveUpper
        boundedLower.le boundedUpper.le grade source flat)

/-- The same original smooth Cartesian source gives a compatible family on
arbitrary moving collars, at every inserted grade, with zero independently
prescribed boundary data. No smoothness or solution-family premise occurs. -/
theorem actualOriginalSourceSequence_compatible (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (radii : ℕ → ℝ) (positive : ∀ index, 0 < radii index) (bounded : ∀ index, radii index < 1) (grade : ℕ) :
    let data := fun index => actualOriginalSourceDatum parameters L rho epsilon field small
      (radii index) (positive index) (bounded index) grade source flat
    (∀ first second (included : radii first ≤ radii second),
      originalFullSourceRestriction parameters (radii first) (radii second) included (data first).val.ofLp.1 =
        (data second).val.ofLp.1) ∧
    (∀ index, (data index).val.ofLp.2 = 0) := by
  dsimp only
  exact ⟨fun first second included => actualOriginalSourceDatum_restrict parameters L rho epsilon field small
    (radii first) (radii second) included (positive first) (positive second) (bounded first) (bounded second) grade source flat,
    fun _ => rfl⟩

end Grad.ExhaustionSourceAllocation
