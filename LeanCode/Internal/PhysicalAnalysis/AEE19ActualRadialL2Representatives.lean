import AEE18ActualClassicalDerivativeCurve

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators ENNReal
namespace Grad.AnnularLowCompletion
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowVolterra
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem scalarOne_real_smul (scalar : ℝ) (value : ℂ) :
    scalarOne (scalar • value) = scalar • scalarOne value :=
  (scalarOne.restrictScalars ℝ).map_smul scalar value

/-- The actual section determines the L2 value coordinate of the accepted
radial graph; no arbitrary pointwise representative is chosen. -/
theorem weightedRadial_value_ae_of_section (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : WeightedRadialH1 1 lower) (value : ℝ → ComplexEuclidean 1)
    (sectionLaw : ∀ radius : Icc lower 1, weightedRadialSection 1 lower positive bounded field radius = value radius.val) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      collarH1Coordinate (ComplexEuclidean 1) lower 0 (weightedToOrdinary 1 lower positive bounded.le field) radius = value radius := by
  let sectionValue := weightedRadialSection 1 lower positive bounded field
  have representative := (collarContinuous_memLp (ComplexEuclidean 1) lower
    (radialSectionExtension 1 lower bounded.le sectionValue)).coeFn_toLp
  change ∀ᵐ radius ∂volume.restrict (Icc lower 1),
    radialSectionL2 1 lower positive bounded.le sectionValue radius = radialSectionExtension 1 lower bounded.le sectionValue radius at representative
  rw [weightedRadialSection_bulk] at representative
  filter_upwards [representative, ae_restrict_mem measurableSet_Icc] with radius representative inside
  rw [representative]
  change sectionValue (radialClamp lower bounded.le radius) = _
  rw [radialClamp_eq lower bounded.le radius inside]
  exact sectionLaw ⟨radius, inside⟩

theorem scalarRadialRealization_slope_ae (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (initial : ℂ) (derivative : C(ℝ, ℂ)) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      collarH1Coordinate (ComplexEuclidean 1) lower 1 (weightedToOrdinary 1 lower positive bounded.le
        (scalarRadialRealization lower positive bounded initial derivative)) radius = scalarOne (derivative radius) := by
  rw [scalarRadialRealization_slope]
  exact (collarContinuous_memLp (ComplexEuclidean 1) lower (scalarOneCurve derivative)).coeFn_toLp

end Grad.AnnularLowCompletion
