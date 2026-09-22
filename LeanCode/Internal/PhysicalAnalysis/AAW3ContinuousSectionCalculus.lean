import AAW2PhysicalODEBootstrap
import AAR26OriginalInnerBoundary

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

def annularCurveSection (lower : ℝ) (curve : C(ℝ, ComplexEuclidean 1)) : RadialContinuousSection 1 lower :=
  ⟨fun radius => curve radius.val, curve.continuous.comp continuous_subtype_val⟩

theorem annularSectionExtension_eval (lower : ℝ) (bounded : lower ≤ 1)
    (sectionValue : RadialContinuousSection 1 lower) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    radialSectionExtension 1 lower bounded sectionValue radius = sectionValue ⟨radius, inside⟩ := by
  change sectionValue (radialClamp lower bounded radius) = _
  rw [radialClamp_eq lower bounded radius inside]

/-- Smoothness is imposed on the physical, phase-decoded source itself. -/
theorem annularCurveSection_bulk_of_ae (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (source : CollarL2 (ComplexEuclidean 1) lower) (curve : C(ℝ, ComplexEuclidean 1))
    (same : source =ᵐ[volume.restrict (Icc lower 1)] curve) :
    radialSectionL2 1 lower positive bounded.le (annularCurveSection lower curve) = source := by
  apply Lp.ext
  filter_upwards [radialSectionL2_ae 1 lower positive bounded.le (annularCurveSection lower curve),
    same, ae_restrict_mem measurableSet_Icc] with radius representative sourceLaw inside
  rw [← representative, annularSectionExtension_eval lower bounded.le _ radius inside, sourceLaw]
  rfl

theorem annularSection_derivative (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (value derivative : CollarL2 (ComplexEuclidean 1) lower)
    (weak : CollarWeakDerivative lower value derivative)
    (representative derivativeSection : RadialContinuousSection 1 lower)
    (bulk : radialSectionL2 1 lower positive bounded.le representative = value)
    (slope : radialSectionL2 1 lower positive bounded.le derivativeSection = derivative)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (radialSectionExtension 1 lower bounded.le representative)
      (derivativeSection ⟨radius, inside⟩) (Icc lower 1) radius := by
  have same : derivative =ᵐ[volume.restrict (Icc lower 1)]
      radialSectionExtension 1 lower bounded.le derivativeSection := by
    rw [← slope]
    filter_upwards [radialSectionL2_ae 1 lower positive bounded.le derivativeSection] with point equality
    exact equality.symm
  have result := annularSection_derivative_of_weak lower positive bounded value derivative weak
    representative bulk (radialSectionExtension 1 lower bounded.le derivativeSection) same radius inside
  rw [annularSectionExtension_eval lower bounded.le derivativeSection radius inside] at result
  exact result

end Grad.AnnularRegularity
