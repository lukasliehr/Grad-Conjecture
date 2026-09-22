import AEE28UniformOriginalLowInverse

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

theorem lowReferenceInverse_incoming (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1) (data : LowEnergyData lower) :
    lowIncomingTrace lower length positive bounded
      (lowReferenceInverse parameters length lower lengthPositive positive bounded data) = data.ofLp.2 :=
  congrArg (fun result : LowEnergyData lower => result.ofLp.2)
    (lowReferenceDataOperator_inverse parameters length lower lengthPositive positive bounded data)

/-- Endpoint equality is a consequence of the weak graph's actual trace. -/
theorem lowReferenceInverse_endpoint (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (data : LowEnergyData lower) (index : LowAnnularIndex) :
    lowEnergyEndpoint lower length positive bounded 0
      (lowReferenceInverse parameters length lower lengthPositive positive bounded data) index =
      lowDataIncoming lower length data index := by
  apply smul_right_injective (ComplexEuclidean 1) (lowIncomingFactor_pos lower length positive index.2).ne'
  change (lower ^ (-(7 / 4 : ℝ)) * (Real.sqrt (lowMu length lower index.2.val.2))⁻¹) • _ = _
  rw [← lowIncomingTrace_apply, lowReferenceInverse_incoming]
  exact (lowDataIncoming_normalization lower length positive data index).symm

/-- The completed inverse solves every literal BE10 weak row on the original
collar; the coefficient is the actual reference matrix, for all four modes
and every axial cell. -/
theorem lowReferenceInverse_row_ae (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (data : LowEnergyData lower) (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowEnergyDerivative lower length positive index
        (lowReferenceInverse parameters length lower lengthPositive positive bounded data).val radius =
      lowReferenceMatrix parameters length radius index.2 index.1 0 •
        lowEnergyValue lower positive (0, index.2)
          (lowReferenceInverse parameters length lower lengthPositive positive bounded data).val radius +
      lowReferenceMatrix parameters length radius index.2 index.1 1 •
        lowEnergyValue lower positive (1, index.2)
          (lowReferenceInverse parameters length lower lengthPositive positive bounded data).val radius +
      lowMu length radius index.2.val.2 • lowDataResidual lower positive data index radius := by
  have residual := lowReferenceDataResidual_ae parameters length lower lengthPositive positive bounded
    (lowReferenceInverse parameters length lower lengthPositive positive bounded data) index
  rw [lowReferenceDataOperator_inverse] at residual
  filter_upwards [residual,
    collarScalar_ae 1 lower (lowMuInverseCurve lower length positive index.2.val.2)
      (lowEnergyDerivative lower length positive index (lowReferenceInverse parameters length lower lengthPositive positive bounded data).val),
    ae_restrict_mem measurableSet_Icc] with radius residual scaled member
  rw [residual, scaled]
  change _ = _ + _ + lowMu length radius index.2.val.2 •
    ((lowMu length (max lower radius) index.2.val.2)⁻¹ • _ - _)
  rw [max_eq_right member.1]
  exact (row_residual_cancel _ _ _ (lowMu_pos length radius index.2.val.2 (positive.trans_le member.1)).ne' _ _ _).symm

end Grad.AnnularLowCompletion
