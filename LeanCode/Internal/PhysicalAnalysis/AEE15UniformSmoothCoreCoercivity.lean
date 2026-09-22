import AEE14OriginalSummedSmoothNorms

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

/-- Sum both original low components without changing the lp carrier.
The component-swap reindexing merely counts each proved pair twice. -/
theorem lowSmoothGraph_coercivity (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (core : LowAnnularIndex →₀ SmoothRadialCore 1) :
    ‖lowSmoothGraph lower length positive bounded core‖ ^ 2 ≤
      lowReferenceGraphConstant parameters length *
        ‖lowReferenceDataOperator parameters length lower lengthPositive positive bounded
          (lowSmoothGraph lower length positive bounded core)‖ ^ 2 := by
  let graph := lowCoreGraphSquare length lower core
  let data := lowCoreDataSquare parameters length lower positive core
  have graphSummable : Summable graph := lowCoreGraphSquare_summable lower length positive bounded core
  have dataSummable : Summable data := lowCoreDataSquare_summable parameters lower length lengthPositive positive bounded core
  have swapGraph : Summable (fun index => graph (lowSwapIndex index)) := lowSwapIndex.summable_iff.mpr graphSummable
  have swapData : Summable (fun index => data (lowSwapIndex index)) := lowSwapIndex.summable_iff.mpr dataSummable
  have pointwise : ∀ index, graph index + graph (lowSwapIndex index) ≤
      lowReferenceGraphConstant parameters length * (data index + data (lowSwapIndex index)) := by
    rintro ⟨row, mode⟩
    fin_cases row
    · simpa [lowSwapIndex, graph, data] using
        lowCorePair_coercivity parameters length lower lengthPositive positive bounded.le core mode
    · simpa [lowSwapIndex, graph, data, add_comm] using
        lowCorePair_coercivity parameters length lower lengthPositive positive bounded.le core mode
  have summed := (graphSummable.add swapGraph).tsum_le_tsum pointwise
    ((dataSummable.add swapData).mul_left (lowReferenceGraphConstant parameters length))
  have graphSum : (∑' index, (graph index + graph (lowSwapIndex index))) =
      (∑' index, graph index) + ∑' index, graph (lowSwapIndex index) := graphSummable.tsum_add swapGraph
  have dataSum : (∑' index, (data index + data (lowSwapIndex index))) =
      (∑' index, data index) + ∑' index, data (lowSwapIndex index) := dataSummable.tsum_add swapData
  rw [graphSum, tsum_mul_left, dataSum, lowSwapIndex.tsum_eq graph, lowSwapIndex.tsum_eq data] at summed
  rw [lowSmoothGraph_norm_sq, lowSmoothGraph_data_norm_sq]
  nlinarith only [summed]

end Grad.AnnularLowCompletion
