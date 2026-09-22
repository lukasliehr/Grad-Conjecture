import AAW3ContinuousSectionCalculus

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

def annularSolutionXiCurve (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (mode : HighAnnularMode) : C(ℝ, ComplexEuclidean 1) :=
  radialSectionExtension 1 lower bounded.le
    (annularPhysicalValueSection parameters lower length positive bounded mode
      (annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue))

def annularSolutionQCurve (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (mode : HighAnnularMode) : C(ℝ, ComplexEuclidean 1) :=
  radialSectionExtension 1 lower bounded.le
    (annularPhysicalQSection parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode)

def annularSolutionPCurve (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (mode : HighAnnularMode) : C(ℝ, ComplexEuclidean 1) :=
  radialSectionExtension 1 lower bounded.le
    (annularPhysicalPSection parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode)

/-- The genuine physical xi derivative, including both endpoints. Only
continuity of the actual physical f coefficient is required at this step. -/
theorem annularSolutionXi_derivative (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (mode : HighAnnularMode) (f : C(ℝ, ComplexEuclidean 1))
    (fActual : annularDecodeMode parameters lower positive mode (source.1 mode) =ᵐ[volume.restrict (Icc lower 1)] f)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (annularSolutionXiCurve parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode)
      (annularSolutionQCurve parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode radius -
        (2 / radius : ℝ) • annularSolutionXiCurve parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode radius +
        f radius) (Icc lower 1) radius := by
  let field := annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
  let xi := annularPhysicalValueSection parameters lower length positive bounded mode field
  let q := annularPhysicalQSection parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode
  let derivativeSection := q - radialSectionScalar lower (annularRadialCurve lower positive) xi + annularCurveSection lower f
  have slope : radialSectionL2 1 lower positive bounded.le derivativeSection =
      annularPhysicalSlope parameters lower length positive bounded.le mode field := by
    change radialSectionL2 1 lower positive bounded.le
      (q - radialSectionScalar lower (annularRadialCurve lower positive) xi + annularCurveSection lower f) = _
    rw [map_add, map_sub, radialSectionL2_scalar,
      annularPhysicalQSection_bulk, annularPhysicalValueSection_bulk,
      annularCurveSection_bulk_of_ae lower positive bounded _ f fActual]
    have row := annularPhysical_first_row parameters lower length positive lengthPositive widthHalf widthLength bounded.le field source.1 mode
    rw [annularPhysicalP_D] at row
    have row' : annularPhysicalSlope parameters lower length positive bounded.le mode field +
        collarScalar 1 lower (annularRadialCurve lower positive)
          (annularPhysicalValue parameters lower length positive bounded.le mode field) -
        annularPhysicalQ parameters lower length positive lengthPositive widthHalf widthLength field source.1 mode =
        annularDecodeMode parameters lower positive mode (source.1 mode) := by
      simpa only [sub_eq_add_neg] using row
    have rearranged := eq_sub_iff_add_eq.mpr (sub_eq_iff_eq_add.mp row')
    exact (rearranged.trans (by abel)).symm
  have actual := annularSection_derivative lower positive bounded _ _
    (annularPhysicalValue_weak parameters lower length positive bounded.le mode field) xi derivativeSection
    (annularPhysicalValueSection_bulk parameters lower length positive bounded mode field) slope radius inside
  have xiAt := annularSectionExtension_eval lower bounded.le xi radius inside
  have qAt := annularSectionExtension_eval lower bounded.le q radius inside
  change annularSolutionXiCurve parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode radius = _ at xiAt
  change annularSolutionQCurve parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue mode radius = _ at qAt
  change HasDerivWithinAt _ (q ⟨radius, inside⟩ - (2 / max lower radius : ℝ) • xi ⟨radius, inside⟩ + f radius) _ _ at actual
  rw [max_eq_right inside.1, ← xiAt, ← qAt] at actual
  exact actual

end Actual
end Grad.AnnularRegularity
