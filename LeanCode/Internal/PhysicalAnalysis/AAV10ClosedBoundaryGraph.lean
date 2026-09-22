import AAV9ActualGraphBoundary

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularConverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.GaugeCoefficients.Physical.WeightedTrace

section Graph
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

local notation "DG" => annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength

def annularGraphSource : DG →L[ℂ] AnnularForcing lower :=
  (ContinuousLinearMap.snd ℂ (annularEnergySpace lower length positive) (AnnularForcing lower)).comp (DG).subtypeL

def annularGraphBeta : DG →L[ℂ] AnnularBoundary :=
  (ContinuousLinearMap.snd ℂ (AnnularBulk lower) AnnularBoundary).comp
    ((ContinuousLinearMap.snd ℂ (AnnularBulk lower) (AnnularBulk lower × AnnularBoundary)).comp
      ((ContinuousLinearMap.snd ℂ (AnnularBulk lower) (AnnularBulk lower × (AnnularBulk lower × AnnularBoundary))).comp
        (annularGraphSource parameters lower length positive lengthPositive widthHalf widthLength)))

/-- Closed original weak graph with its actual natural outer boundary
coordinate. No trace or variational law is added as an independent field. -/
def annularBoundaryFluxGraph : Submodule ℂ DG :=
  (annularDataFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength 1 +
    annularGraphBeta parameters lower length positive lengthPositive widthHalf widthLength).ker

theorem annularBoundaryFluxGraph_closed : IsClosed (annularBoundaryFluxGraph parameters lower length positive bounded
    lengthPositive widthHalf widthLength : Set DG) :=
  (annularDataFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength 1 +
    annularGraphBeta parameters lower length positive lengthPositive widthHalf widthLength).isClosed_ker

instance annularBoundaryFluxGraph_complete : CompleteSpace
    (annularBoundaryFluxGraph parameters lower length positive bounded lengthPositive widthHalf widthLength) :=
  (annularBoundaryFluxGraph_closed parameters lower length positive bounded lengthPositive widthHalf widthLength).completeSpace_coe

def annularBoundaryGraphInverse : (AnnularForcing lower × AnnularBoundary) →L[ℂ]
    annularBoundaryFluxGraph parameters lower length positive bounded lengthPositive widthHalf widthLength :=
  (annularSolvedDataGraph parameters lower length positive bounded lengthPositive widthHalf widthLength).codRestrict
    (annularBoundaryFluxGraph parameters lower length positive bounded lengthPositive widthHalf widthLength) (by
      intro data
      change annularDataFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength 1
        (annularSolvedDataGraph parameters lower length positive bounded lengthPositive widthHalf widthLength data) + data.1.2.2.2 = 0
      rw [annularSolvedData_outer, neg_add_cancel])

def annularBoundaryGraphForward :
    annularBoundaryFluxGraph parameters lower length positive bounded lengthPositive widthHalf widthLength →L[ℂ]
      (AnnularForcing lower × AnnularBoundary) :=
  ((annularGraphSource parameters lower length positive lengthPositive widthHalf widthLength).prod
    ((annularEnergyTrace lower length positive bounded lengthPositive 0).comp
      ((ContinuousLinearMap.fst ℂ (annularEnergySpace lower length positive) (AnnularForcing lower)).comp (DG).subtypeL))).comp
    (annularBoundaryFluxGraph parameters lower length positive bounded lengthPositive widthHalf widthLength).subtypeL

end Graph
end Grad.AnnularConverse
