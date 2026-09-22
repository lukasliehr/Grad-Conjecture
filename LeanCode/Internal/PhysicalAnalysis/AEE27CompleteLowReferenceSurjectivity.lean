import AEE26OriginalSingleDataRange

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

/-- The actual BE18 map is onto the full completed residual/incoming space. -/
theorem lowReferenceDataOperator_surjective (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1) :
    Function.Surjective (lowReferenceDataOperator parameters length lower lengthPositive positive bounded) := by
  let target := LinearMap.range (lowReferenceDataOperator parameters length lower lengthPositive positive bounded).toLinearMap
  have closed : IsClosed (target : Set (LowEnergyData lower)) :=
    lowReferenceDataOperator_closed_range parameters length lower lengthPositive positive bounded
  have bulkMember (value : LowEnergyBulk lower) : lowBulkDataInjection lower value ∈ target := by
    have convergence : HasSum (fun index : LowAnnularIndex => lowBulkSingleData lower index (value index))
        (lowBulkDataInjection lower value) :=
      (lp.hasSum_single (by norm_num) value).map (lowBulkDataInjection lower).toAddMonoidHom (lowBulkDataInjection lower).continuous
    apply closed.mem_of_tendsto convergence
    exact Filter.Eventually.of_forall (fun support => target.sum_mem (fun index _ =>
      lowBulkSingle_mem_range parameters length lower lengthPositive positive bounded index (value index)))
  have boundaryMember (value : LowEnergyBoundary) : lowBoundaryDataInjection lower value ∈ target := by
    have convergence : HasSum (fun index : LowAnnularIndex => lowBoundarySingleData lower index (value index))
        (lowBoundaryDataInjection lower value) :=
      (lp.hasSum_single (by norm_num) value).map (lowBoundaryDataInjection lower).toAddMonoidHom (lowBoundaryDataInjection lower).continuous
    apply closed.mem_of_tendsto convergence
    exact Filter.Eventually.of_forall (fun support => target.sum_mem (fun index _ =>
      lowBoundarySingle_mem_range parameters length lower lengthPositive positive bounded index (value index)))
  intro data
  have member := target.add_mem (bulkMember data.ofLp.1) (boundaryMember data.ofLp.2)
  have decomposition : lowBulkDataInjection lower data.ofLp.1 + lowBoundaryDataInjection lower data.ofLp.2 = data :=
    congrArg (WithLp.toLp 2) (Prod.ext (add_zero _) (zero_add _))
  exact decomposition ▸ member

theorem lowReferenceDataOperator_bijective (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1) :
    Function.Bijective (lowReferenceDataOperator parameters length lower lengthPositive positive bounded) :=
  ⟨lowReferenceDataOperator_injective parameters length lower lengthPositive positive bounded,
    lowReferenceDataOperator_surjective parameters length lower lengthPositive positive bounded⟩

end Grad.AnnularLowCompletion
