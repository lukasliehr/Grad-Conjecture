import AAQ9BoundedComplexFluxTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularFluxTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

section SolutionGraph
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

def annularFluxCoordinates : AnnularFluxAmbient lower length positive →L[ℂ] AnnularFluxGraphAmbient lower :=
  (annularFluxQ parameters lower length positive lengthPositive widthHalf widthLength).prod
    (annularFluxSlope parameters lower length positive lengthPositive widthHalf widthLength)

/-- The literal weak flux graph on the original energy state and prescribed
undifferentiated sources. It is the exact preimage of the genuine radial graph. -/
def annularFluxDataGraph : Submodule ℂ (AnnularFluxAmbient lower length positive) :=
  (annularFluxWeakGraph lower positive).comap
    (annularFluxCoordinates parameters lower length positive lengthPositive widthHalf widthLength).toLinearMap

theorem annularFluxDataGraph_closed :
    IsClosed (annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength :
      Set (AnnularFluxAmbient lower length positive)) :=
  (annularFluxWeakGraph_closed lower positive).preimage
    (annularFluxCoordinates parameters lower length positive lengthPositive widthHalf widthLength).continuous

instance annularFluxDataGraph_complete :
    CompleteSpace (annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength) :=
  (annularFluxDataGraph_closed parameters lower length positive lengthPositive widthHalf widthLength).completeSpace_coe

def annularDataFluxGraph :
    annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength →L[ℂ]
      annularFluxWeakGraph lower positive :=
  ((annularFluxCoordinates parameters lower length positive lengthPositive widthHalf widthLength).comp
    (annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength).subtypeL).codRestrict
      (annularFluxWeakGraph lower positive) (fun data => data.property)

def annularDataFluxTrace (endpoint : Fin 2) :
    annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength →L[ℂ] AnnularBoundary :=
  (annularFluxTrace lower positive bounded endpoint).comp
    (annularDataFluxGraph parameters lower length positive lengthPositive widthHalf widthLength)

def annularSolutionWithSource : (AnnularForcing lower × AnnularBoundary) →L[ℂ] AnnularFluxAmbient lower length positive :=
  (annularVariationalInverse parameters lower length positive bounded lengthPositive widthHalf widthLength).prod
    (ContinuousLinearMap.fst ℂ _ _)

theorem annularSolutionWithSource_mem (data : AnnularForcing lower × AnnularBoundary) :
    annularSolutionWithSource parameters lower length positive bounded lengthPositive widthHalf widthLength data ∈
      annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength := by
  intro mode
  let field := annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2
  let pair : AnnularFluxAmbient lower length positive := (field, data.1)
  let ν := Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2
  have ordinary := annularFluxSlope_ordinary parameters lower length positive lengthPositive widthHalf widthLength bounded.le pair mode
  have derivative : (ν : ℝ) • radialOrdinary 1 lower positive
      (annularFluxSlope parameters lower length positive lengthPositive widthHalf widthLength pair mode) =
      annularNormalizedQSlope parameters lower length positive lengthPositive widthHalf widthLength bounded.le field data.1 mode := by
    have scaled := congrArg (fun value : CollarL2 (ComplexEuclidean 1) lower => (ν : ℝ) • value) ordinary
    exact scaled.trans (by
      change (ν : ℝ) • ((ν⁻¹ : ℝ) • _) = _
      rw [smul_smul, mul_inv_cancel₀ (annularFrequency_pos mode).ne', one_smul])
  have weak := annularNormalizedQ_weak parameters lower length positive lengthPositive widthHalf widthLength bounded data.1 data.2 mode
  change CollarWeakDerivative lower
    (radialOrdinary 1 lower positive (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field data.1.1 mode))
    ((ν : ℝ) • radialOrdinary 1 lower positive
      (annularFluxSlope parameters lower length positive lengthPositive widthHalf widthLength pair mode))
  exact (congrArg (fun slope => CollarWeakDerivative lower
    (radialOrdinary 1 lower positive (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field data.1.1 mode)) slope) derivative).mpr weak

/-- The actual variational inverse takes values in the independently defined
closed graph. Membership follows from the proved physical weak row. -/
def annularSolvedDataGraph : (AnnularForcing lower × AnnularBoundary) →L[ℂ]
    annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength :=
  (annularSolutionWithSource parameters lower length positive bounded lengthPositive widthHalf widthLength).codRestrict
    (annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength)
    (annularSolutionWithSource_mem parameters lower length positive bounded lengthPositive widthHalf widthLength)

def annularSolvedFlux : (AnnularForcing lower × AnnularBoundary) →L[ℂ] annularFluxWeakGraph lower positive :=
  (annularDataFluxGraph parameters lower length positive lengthPositive widthHalf widthLength).comp
    (annularSolvedDataGraph parameters lower length positive bounded lengthPositive widthHalf widthLength)

def annularSolutionFluxTrace (endpoint : Fin 2) : (AnnularForcing lower × AnnularBoundary) →L[ℂ] AnnularBoundary :=
  (annularFluxTrace lower positive bounded endpoint).comp
    (annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength)

theorem annularSolvedFlux_value (data : AnnularForcing lower × AnnularBoundary) :
    (annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength data).val.1 =
      annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength
        (annularVariationalInverse parameters lower length positive bounded lengthPositive widthHalf widthLength data) data.1.1 := rfl

end SolutionGraph
end Grad.AnnularFluxTrace
