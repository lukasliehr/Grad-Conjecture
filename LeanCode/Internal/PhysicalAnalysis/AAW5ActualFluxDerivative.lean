import AAW4ActualFieldDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

section Actual
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- AG23 holds classically on the closed collar as soon as its actual
physical G3 and F2 are continuous. No radial source derivative enters. -/
theorem annularSolutionQ_derivative (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (mode : HighAnnularMode) (g h : C(ℝ, ComplexEuclidean 1))
    (gActual : annularDecodeMode parameters lower positive mode (source.2.1 mode) =ᵐ[volume.restrict (Icc lower 1)] g)
    (hActual : annularDecodeMode parameters lower positive mode (source.2.2.1 mode) =ᵐ[volume.restrict (Icc lower 1)] h)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (annularSolutionQCurve parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode)
      ((1 / radius : ℝ) • annularSolutionQCurve parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode radius +
        annularPotential length radius mode.val.1 mode.val.2 •
          annularSolutionXiCurve parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode radius -
        (4 : ℝ) • ((1 / radius : ℝ) • ((1 / radius : ℝ) •
          annularSolutionXiCurve parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode radius)) -
        annularDSymbol mode • g radius - annularCellSymbol length mode • h radius) (Icc lower 1) radius := by
  let field := annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
  let xi := annularPhysicalValueSection parameters lower length positive bounded mode field
  let q := annularPhysicalQSection parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode
  let inverse := annularInverseRadiusCurve lower positive
  let potential := annularPotentialCurve lower length positive mode
  let derivativeSection := radialSectionScalar lower inverse q + radialSectionScalar lower potential xi -
    (4 : ℝ) • radialSectionScalar lower inverse (radialSectionScalar lower inverse xi) -
    annularDSymbol mode • annularCurveSection lower g - annularCellSymbol length mode • annularCurveSection lower h
  have slope : radialSectionL2 1 lower positive bounded.le derivativeSection =
      annularPhysicalQSlope parameters lower length positive lengthPositive widthHalf widthLength bounded.le field source mode := by
    change radialSectionL2 1 lower positive bounded.le
      (radialSectionScalar lower inverse q + radialSectionScalar lower potential xi -
        (4 : ℝ) • radialSectionScalar lower inverse (radialSectionScalar lower inverse xi) -
        annularDSymbol mode • annularCurveSection lower g - annularCellSymbol length mode • annularCurveSection lower h) = _
    simp only [map_add, map_sub, map_smul, radialSectionL2_complex_smul, radialSectionL2_scalar]
    rw [annularPhysicalQSection_bulk, annularPhysicalValueSection_bulk,
      annularCurveSection_bulk_of_ae lower positive bounded _ g gActual,
      annularCurveSection_bulk_of_ae lower positive bounded _ h hActual]
    exact (annularPhysicalQSlope_formula parameters lower length positive lengthPositive widthHalf widthLength bounded.le field source mode).symm
  have actual := annularSection_derivative lower positive bounded _ _
    (annularPhysicalQ_weak parameters lower length positive lengthPositive widthHalf widthLength bounded source innerValue mode) q derivativeSection
    (annularPhysicalQSection_bulk parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode) slope radius inside
  have xiAt := annularSectionExtension_eval lower bounded.le xi radius inside
  have qAt := annularSectionExtension_eval lower bounded.le q radius inside
  change annularSolutionXiCurve parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode radius = _ at xiAt
  change annularSolutionQCurve parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode radius = _ at qAt
  change HasDerivWithinAt _ ((1 / max lower radius : ℝ) • q ⟨radius, inside⟩ +
    annularPotentialCurve lower length positive mode radius • xi ⟨radius, inside⟩ -
    (4 : ℝ) • ((1 / max lower radius : ℝ) • ((1 / max lower radius : ℝ) • xi ⟨radius, inside⟩)) -
    annularDSymbol mode • g radius - annularCellSymbol length mode • h radius) _ _ at actual
  rw [max_eq_right inside.1, annularPotentialCurve_literal lower length positive mode radius inside.1,
    ← xiAt, ← qAt] at actual
  exact actual

end Actual
end Grad.AnnularRegularity
