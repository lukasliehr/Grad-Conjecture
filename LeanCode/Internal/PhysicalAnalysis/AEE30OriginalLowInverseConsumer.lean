import AEE29ActualInverseRowsAndTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators ENNReal
namespace Grad.AnnularLowCompletion
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowVolterra
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Uniform reference inverse on every original annular collar, at the
literal BE18 norm and without an extra high-sector radial tilt. -/
theorem originalLowReferenceInverse_uniform (parameters : PhaseParameters) (length : ℝ)
    (lengthPositive : 0 < length) :
    ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1),
      ‖lowReferenceInverse parameters length lower lengthPositive positive bounded‖ ≤
        Real.sqrt (lowReferenceGraphConstant parameters length) := by
  intro lower positive bounded
  exact ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    (lowReferenceInverse_bound parameters length lower lengthPositive positive bounded)

/-- Immediate original-data consumer: the same complete solution has the
exact residual, genuine incoming trace, unique graph representative, and
radius-independent full Y bound. -/
theorem originalLowReferenceInverse_consumer (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1) (data : LowEnergyData lower) :
    lowReferenceDataOperator parameters length lower lengthPositive positive bounded
      (lowReferenceInverse parameters length lower lengthPositive positive bounded data) = data ∧
    ‖lowReferenceInverse parameters length lower lengthPositive positive bounded data‖ ≤
      Real.sqrt (lowReferenceGraphConstant parameters length) * ‖data‖ ∧
    (∀ field : lowEnergyGraph lower length positive,
      lowReferenceDataOperator parameters length lower lengthPositive positive bounded field = data →
        field = lowReferenceInverse parameters length lower lengthPositive positive bounded data) ∧
    (∀ index : LowAnnularIndex,
      lowEnergyEndpoint lower length positive bounded 0
        (lowReferenceInverse parameters length lower lengthPositive positive bounded data) index =
        lowDataIncoming lower length data index) ∧
    (∀ index : LowAnnularIndex, ∀ radius : Icc lower (1 : ℝ),
      lowPhysicalFactor parameters length radius.val index •
        lowPhysicalSection parameters lower length positive bounded
          (lowReferenceInverse parameters length lower lengthPositive positive bounded data) index radius =
      lowEnergySection lower length positive bounded
        (lowReferenceInverse parameters length lower lengthPositive positive bounded data) index radius) := by
  refine ⟨lowReferenceDataOperator_inverse parameters length lower lengthPositive positive bounded data,
    lowReferenceInverse_bound parameters length lower lengthPositive positive bounded data, ?_,
    lowReferenceInverse_endpoint parameters length lower lengthPositive positive bounded data, ?_⟩
  · intro field same
    apply lowReferenceDataOperator_injective parameters length lower lengthPositive positive bounded
    rw [same, lowReferenceDataOperator_inverse]
  · exact lowPhysicalSection_encode parameters lower length positive bounded _

end Grad.AnnularLowCompletion
