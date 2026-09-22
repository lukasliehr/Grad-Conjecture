import AEE8LiteralReferenceResidualIdentity

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

def lowCoreResidualCurve (parameters : PhaseParameters) (length lower : ℝ) (positive : 0 < lower)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (index : LowAnnularIndex) : C(ℝ, ComplexEuclidean 1) where
  toFun radius := lowMuInverseCurve lower length positive index.2.val.2 radius • (core index).val.val.2 radius -
    (lowNormalizedReferenceCurve parameters length lower positive index.2 index.1 0 radius • (core (0, index.2)).val.val.1 radius +
      lowNormalizedReferenceCurve parameters length lower positive index.2 index.1 1 radius • (core (1, index.2)).val.val.1 radius)
  continuous_toFun := ((lowMuInverseCurve lower length positive index.2.val.2).continuous.smul
    (core index).val.val.2.continuous).sub
    (((lowNormalizedReferenceCurve parameters length lower positive index.2 index.1 0).continuous.smul
      (core (0, index.2)).val.val.1.continuous).add
      ((lowNormalizedReferenceCurve parameters length lower positive index.2 index.1 1).continuous.smul
        (core (1, index.2)).val.val.1.continuous))

theorem lowCoreResidualCurve_actual (parameters : PhaseParameters) (length lower : ℝ) (positive : 0 < lower)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (index : LowAnnularIndex) (radius : ℝ) (inside : lower ≤ radius) :
    lowCoreResidualCurve parameters length lower positive core index radius =
      (lowMu length radius index.2.val.2)⁻¹ • (core index).val.val.2 radius -
      ((lowReferenceMatrix parameters length radius index.2 index.1 0 / lowMu length radius index.2.val.2) •
        (core (0, index.2)).val.val.1 radius +
       (lowReferenceMatrix parameters length radius index.2 index.1 1 / lowMu length radius index.2.val.2) •
        (core (1, index.2)).val.val.1 radius) := by
  change lowMuInverseCurve lower length positive index.2.val.2 radius • (core index).val.val.2 radius - _ = _
  rw [lowNormalizedReferenceCurve_actual parameters length lower positive index.2 index.1 0 radius inside,
    lowNormalizedReferenceCurve_actual parameters length lower positive index.2 index.1 1 radius inside]
  change (lowMu length (max lower radius) index.2.val.2)⁻¹ • _ - _ = _
  rw [max_eq_right inside]

theorem lowSmoothGraph_value_ae (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowEnergyValue lower positive index (lowSmoothGraph lower length positive bounded core).val radius =
        (core index).val.val.1 radius := by
  rw [lowSmoothGraph_value]
  exact (collarContinuous_memLp (ComplexEuclidean 1) lower (core index).val.val.1).coeFn_toLp

theorem lowSmoothGraph_normalizedDerivative_ae (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      collarScalar 1 lower (lowMuInverseCurve lower length positive index.2.val.2)
        (lowEnergyDerivative lower length positive index (lowSmoothGraph lower length positive bounded core).val) radius =
      (lowMu length radius index.2.val.2)⁻¹ • (core index).val.val.2 radius := by
  rw [lowSmoothGraph_derivative]
  have multiplier := collarScalar_ae 1 lower (lowMuInverseCurve lower length positive index.2.val.2)
    (collarContinuousL2 (ComplexEuclidean 1) lower (core index).val.val.2)
  have representative := (collarContinuous_memLp (ComplexEuclidean 1) lower (core index).val.val.2).coeFn_toLp
  filter_upwards [multiplier, representative, ae_restrict_mem measurableSet_Icc] with radius multiplier representative inside
  change collarContinuousL2 (ComplexEuclidean 1) lower (core index).val.val.2 radius = (core index).val.val.2 radius at representative
  rw [multiplier, representative]
  change (lowMu length (max lower radius) index.2.val.2)⁻¹ • _ = _
  rw [max_eq_right inside.1]

theorem lowSmoothGraph_dataResidual_ae (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowDataResidual lower positive (lowReferenceDataOperator parameters length lower lengthPositive positive bounded
        (lowSmoothGraph lower length positive bounded core)) index radius =
      lowCoreResidualCurve parameters length lower positive core index radius := by
  filter_upwards [lowReferenceDataResidual_ae parameters length lower lengthPositive positive bounded
      (lowSmoothGraph lower length positive bounded core) index,
    lowSmoothGraph_normalizedDerivative_ae lower length positive bounded core index,
    lowSmoothGraph_value_ae lower length positive bounded core (0, index.2),
    lowSmoothGraph_value_ae lower length positive bounded core (1, index.2),
    ae_restrict_mem measurableSet_Icc] with radius residual slope first second inside
  rw [residual, slope, first, second, lowCoreResidualCurve_actual parameters length lower positive core index radius inside.1]

end Grad.AnnularLowCompletion
