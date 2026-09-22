import AEE7OriginalSmoothGraphRealization

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

/-- Decoding the stored forward residual gives exactly mu^-1(w'-Gref w).
The common rho storage weight cancels through both physical components. -/
theorem lowReferenceDataResidual_ae (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowDataResidual lower positive
        (lowReferenceDataOperator parameters length lower lengthPositive positive bounded field) index radius =
      collarScalar 1 lower (lowMuInverseCurve lower length positive index.2.val.2)
        (lowEnergyDerivative lower length positive index field.val) radius -
      ((lowReferenceMatrix parameters length radius index.2 index.1 0 / lowMu length radius index.2.val.2) •
        lowEnergyValue lower positive (0, index.2) field.val radius +
       (lowReferenceMatrix parameters length radius index.2 index.1 1 / lowMu length radius index.2.val.2) •
        lowEnergyValue lower positive (1, index.2) field.val radius) := by
  let action := lowReferenceBulk parameters length lower lengthPositive positive (field.val 0)
  have residualValue := Lp.coeFn_sub (field.val 1 index) (action index)
  have decoded := collarScalar_ae 1 lower (lowStorageInverse lower positive) (field.val 1 index - action index)
  have actionValue := lowReferenceBulk_ae parameters length lower lengthPositive positive (field.val 0) index
  have firstValue := collarScalar_ae 1 lower (lowStorageInverse lower positive) (field.val 0 (0, index.2))
  have secondValue := collarScalar_ae 1 lower (lowStorageInverse lower positive) (field.val 0 (1, index.2))
  have slopeValue := collarScalar_ae 1 lower (lowStorageInverse lower positive) (field.val 1 index)
  rw [← lowEnergy_normalized_derivative lower length positive field.val index] at slopeValue
  filter_upwards [residualValue, decoded, actionValue, firstValue, secondValue, slopeValue]
    with radius residualValue decoded actionValue firstValue secondValue slopeValue
  change collarScalar 1 lower (lowStorageInverse lower positive) (field.val 1 index - action index) radius =
    collarScalar 1 lower (lowMuInverseCurve lower length positive index.2.val.2)
      (lowEnergyDerivative lower length positive index field.val) radius -
    ((lowReferenceMatrix parameters length radius index.2 index.1 0 / lowMu length radius index.2.val.2) •
      collarScalar 1 lower (lowStorageInverse lower positive) (field.val 0 (0, index.2)) radius +
     (lowReferenceMatrix parameters length radius index.2 index.1 1 / lowMu length radius index.2.val.2) •
      collarScalar 1 lower (lowStorageInverse lower positive) (field.val 0 (1, index.2)) radius)
  rw [decoded, residualValue]
  simp only [Pi.sub_apply]
  change action index radius = _ at actionValue
  rw [actionValue, firstValue, secondValue, slopeValue]
  module

end Grad.AnnularLowCompletion
