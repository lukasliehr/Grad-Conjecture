import SBT12RestrictionEndpoint
import TRM11PublicBoundary

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.SourceBoundaryTrace
open Grad.ClosedJets Grad.SourceCollarDivision Grad.SourceCollarAngular
open Grad.GaugeCoefficients.Physical.WeightedTrace

def mappedSmoothCurve {sourceDimension targetDimension : ℕ}
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (core : collarSmoothGraph (ComplexEuclidean sourceDimension)) :
    collarSmoothGraph (ComplexEuclidean targetDimension) :=
  ⟨(⟨fun radius => mapping (core.val.1 radius), mapping.continuous.comp core.val.1.continuous⟩,
      ⟨fun radius => mapping (core.val.2 radius), mapping.continuous.comp core.val.2.continuous⟩),
    fun radius => (mapping.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt radius (core.property radius)⟩

theorem weightedCurve_valueMap {sourceDimension targetDimension : ℕ} (lower : ℝ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (curve : C(ℝ, ComplexEuclidean sourceDimension)) :
    radialValueMap lower mapping (weightedCurveLinear sourceDimension lower curve) =
      weightedCurveLinear targetDimension lower
        ⟨fun radius => mapping (curve radius), mapping.continuous.comp curve.continuous⟩ := by
  apply Lp.ext
  filter_upwards [mapping.coeFn_compLpL (radialToLp lower curve curve.continuous),
    radialToLp_ae lower curve curve.continuous,
    radialToLp_ae lower (fun radius => mapping (curve radius)) (mapping.continuous.comp curve.continuous)]
    with radius mapped original target
  change mapping.compLpL 2 (volume.restrict (Icc lower 1))
    (radialToLp lower curve curve.continuous) radius =
      radialToLp lower (fun radius => mapping (curve radius)) (mapping.continuous.comp curve.continuous) radius
  rw [mapped, original, target]
  exact (mapping.restrictScalars ℝ).map_smul (Real.sqrt radius) (curve radius)

def endpointValueMap {sourceDimension targetDimension : ℕ} (lower : ℝ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    RadialEndpointAmbient sourceDimension lower →L[ℂ] RadialEndpointAmbient targetDimension lower :=
  ((radialValueMap lower mapping).prodMap (radialValueMap lower mapping)).prodMap mapping

theorem weightedEndpointCore_valueMap {sourceDimension targetDimension : ℕ} (lower : ℝ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (core : collarSmoothGraph (ComplexEuclidean sourceDimension)) :
    endpointValueMap lower mapping (weightedEndpointCore sourceDimension lower core) =
      weightedEndpointCore targetDimension lower (mappedSmoothCurve mapping core) := by
  change ((radialValueMap lower mapping (weightedCurveLinear sourceDimension lower core.val.1),
    radialValueMap lower mapping (weightedCurveLinear sourceDimension lower core.val.2)), _) = _
  rw [weightedCurve_valueMap, weightedCurve_valueMap]
  rfl

theorem radialEndpointGraph_valueMap {sourceDimension targetDimension : ℕ} (lower : ℝ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (point : RadialEndpointAmbient sourceDimension lower)
    (member : point ∈ radialEndpointGraph sourceDimension lower) :
    endpointValueMap lower mapping point ∈ radialEndpointGraph targetDimension lower := by
  apply closure_minimal (s := (LinearMap.range (weightedEndpointCore sourceDimension lower) : Set _))
    (fun point coreMember => ?_)
    (((LinearMap.range (weightedEndpointCore targetDimension lower)).isClosed_topologicalClosure).preimage
      (endpointValueMap lower mapping).continuous) member
  rcases coreMember with ⟨core, rfl⟩
  change endpointValueMap lower mapping (weightedEndpointCore sourceDimension lower core) ∈
    radialEndpointGraph targetDimension lower
  rw [weightedEndpointCore_valueMap]
  exact radialEndpointGraph_core targetDimension lower (mappedSmoothCurve mapping core)

end Grad.SourceBoundaryTrace
