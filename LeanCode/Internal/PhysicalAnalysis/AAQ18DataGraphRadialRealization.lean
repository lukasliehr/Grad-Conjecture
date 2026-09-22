import AAQ10ActualSolutionFluxGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularFluxTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

section GenericData
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

def annularDataRadialFluxGraph
    (data : annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength)
    (mode : HighAnnularMode) : WeightedRadialH1 1 lower :=
  annularFluxRadialGraph lower positive bounded
    (annularDataFluxGraph parameters lower length positive lengthPositive widthHalf widthLength data) mode

theorem annularDataRadialFluxGraph_ordinary_value
    (data : annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength)
    (mode : HighAnnularMode) :
    collarH1Coordinate (ComplexEuclidean 1) lower 0
      (weightedToOrdinary 1 lower positive bounded.le
        (annularDataRadialFluxGraph parameters lower length positive bounded lengthPositive widthHalf widthLength data mode)) =
      radialOrdinary 1 lower positive
        (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength data.val.1 data.val.2.1 mode) :=
  annularFluxRadialGraph_ordinary_value lower positive bounded _ mode

theorem annularDataRadialFluxGraph_ordinary_slope
    (data : annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength)
    (mode : HighAnnularMode) :
    collarH1Coordinate (ComplexEuclidean 1) lower 1
      (weightedToOrdinary 1 lower positive bounded.le
        (annularDataRadialFluxGraph parameters lower length positive bounded lengthPositive widthHalf widthLength data mode)) =
      annularNormalizedQSlope parameters lower length positive lengthPositive widthHalf widthLength bounded.le data.val.1 data.val.2 mode := by
  let ν := Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2
  have slope := annularFluxRadialGraph_ordinary_slope lower positive bounded
    (annularDataFluxGraph parameters lower length positive lengthPositive widthHalf widthLength data) mode
  change collarH1Coordinate (ComplexEuclidean 1) lower 1
      (weightedToOrdinary 1 lower positive bounded.le
        (annularDataRadialFluxGraph parameters lower length positive bounded lengthPositive widthHalf widthLength data mode)) =
      (ν : ℝ) • radialOrdinary 1 lower positive
        (annularFluxSlope parameters lower length positive lengthPositive widthHalf widthLength data.val mode) at slope
  have normalized := annularFluxSlope_ordinary parameters lower length positive lengthPositive widthHalf widthLength bounded.le data.val mode
  have scaled := congrArg (fun value : CollarL2 (ComplexEuclidean 1) lower => (ν : ℝ) • value) normalized
  exact slope.trans (scaled.trans (by
    change (ν : ℝ) • ((ν⁻¹ : ℝ) • _) = _
    rw [smul_smul, mul_inv_cancel₀ (annularFrequency_pos mode).ne', one_smul]))

theorem annularDataRadialFluxGraph_value
    (data : annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength)
    (mode : HighAnnularMode) :
    weightedRadialCoordinate 1 lower 0
      (annularDataRadialFluxGraph parameters lower length positive bounded lengthPositive widthHalf widthLength data mode) =
      annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength data.val.1 data.val.2.1 mode :=
  annularFluxRadialGraph_value lower positive bounded _ mode

end GenericData
end Grad.AnnularFluxTrace
