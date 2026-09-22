import AAQ17ActualWeightedFluxGraph
import AAQ18DataGraphRadialRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularFluxTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace

section Consumer
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)) (angular cell inserted : ℕ)

theorem annularSolutionNaturalPTrace_weighted_norm (endpoint : Fin 2) (data : AnnularForcing lower × AnnularBoundary)
    (grade : HasAnnularDataGrade lower angular cell inserted data)
    (qGrade : HasAnnularLpGrade angular cell inserted (annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data))
    (pGrade : HasAnnularLpGrade angular cell inserted (annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data)) :
    ‖annularLpWeighted angular cell inserted (annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data) pGrade‖ =
      ‖annularLpWeighted angular cell inserted (annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data) qGrade‖ := by
  rw [annularSolutionNaturalPTrace_weighted_identity parameters lower length positive bounded lengthPositive widthHalf widthLength angular cell inserted endpoint data grade pGrade,
    annularSolutionFluxTrace_weighted_identity parameters lower length positive bounded lengthPositive widthHalf widthLength angular cell inserted endpoint data grade qGrade]
  exact annularSolutionNaturalPTrace_norm parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint (annularWeightedData lower angular cell inserted data grade)

/-- Exact AG25–28 conormal conclusion: actual full weak graph, both sharp
endpoint traces, exact D-weighted p norm and unchanged constant at every
inserted/split grade on the original analytic width. -/
theorem annularSharpTrace_consumer (endpoint : Fin 2) (data : AnnularForcing lower × AnnularBoundary)
    (grade : HasAnnularDataGrade lower angular cell inserted data) :
    HasAnnularFluxGrade lower positive angular cell inserted (annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength data) ∧
    HasAnnularLpGrade angular cell inserted (annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data) ∧
    HasAnnularLpGrade angular cell inserted (annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data) ∧
    ∀ (qGrade : HasAnnularLpGrade angular cell inserted (annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data))
      (pGrade : HasAnnularLpGrade angular cell inserted (annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data)),
      ‖annularLpWeighted angular cell inserted (annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data) pGrade‖ =
        ‖annularLpWeighted angular cell inserted (annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data) qGrade‖ ∧
      ‖annularLpWeighted angular cell inserted (annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data) qGrade‖ ≤
        annularFluxPhysicalTraceConstant lower length *
          (‖annularVariationalInverse parameters lower length positive bounded lengthPositive widthHalf widthLength (annularWeightedData lower angular cell inserted data grade)‖ +
            ‖(annularWeightedData lower angular cell inserted data grade).1.1‖ +
            ‖(annularWeightedData lower angular cell inserted data grade).1.2.1‖ +
            ‖(annularWeightedData lower angular cell inserted data grade).1.2.2.1‖) := by
  refine ⟨annularSolvedFlux_hasGrade parameters lower length positive bounded lengthPositive widthHalf widthLength angular cell inserted data grade,
    annularSolutionFluxTrace_hasGrade parameters lower length positive bounded lengthPositive widthHalf widthLength angular cell inserted endpoint data grade,
    annularSolutionNaturalPTrace_hasGrade parameters lower length positive bounded lengthPositive widthHalf widthLength angular cell inserted endpoint data grade, ?_⟩
  intro qGrade pGrade
  exact ⟨annularSolutionNaturalPTrace_weighted_norm parameters lower length positive bounded lengthPositive widthHalf widthLength angular cell inserted endpoint data grade qGrade pGrade,
    annularSolutionFluxTrace_weighted_bound parameters lower length positive bounded lengthPositive widthHalf widthLength angular cell inserted endpoint data grade qGrade⟩

theorem annularSolutionFluxTrace_weightedCut_convergence (endpoint : Fin 2) (data : AnnularForcing lower × AnnularBoundary)
    (grade : HasAnnularDataGrade lower angular cell inserted data)
    (traceGrade : HasAnnularLpGrade angular cell inserted (annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data)) :
    Tendsto (fun support : Finset HighAnnularMode =>
      annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint
        (annularDataCut lower (support : Set HighAnnularMode) (annularWeightedData lower angular cell inserted data grade)))
      atTop (𝓝 (annularLpWeighted angular cell inserted (annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data) traceGrade)) := by
  have convergence := ((annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint).continuous.tendsto
    (annularWeightedData lower angular cell inserted data grade)).comp
      (annularDataCut_tendsto lower (annularWeightedData lower angular cell inserted data grade))
  have same := annularSolutionFluxTrace_weighted_identity parameters lower length positive bounded lengthPositive widthHalf widthLength angular cell inserted endpoint data grade traceGrade
  exact (congrArg (fun value : AnnularBoundary => Tendsto
    (fun support : Finset HighAnnularMode => annularSolutionFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint
      (annularDataCut lower (support : Set HighAnnularMode) (annularWeightedData lower angular cell inserted data grade))) atTop (𝓝 value)) same).mpr convergence

theorem annularSolutionNaturalPTrace_weightedCut_convergence (endpoint : Fin 2) (data : AnnularForcing lower × AnnularBoundary)
    (grade : HasAnnularDataGrade lower angular cell inserted data)
    (traceGrade : HasAnnularLpGrade angular cell inserted (annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data)) :
    Tendsto (fun support : Finset HighAnnularMode =>
      annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint
        (annularDataCut lower (support : Set HighAnnularMode) (annularWeightedData lower angular cell inserted data grade)))
      atTop (𝓝 (annularLpWeighted angular cell inserted (annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint data) traceGrade)) := by
  have convergence := ((annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint).continuous.tendsto
    (annularWeightedData lower angular cell inserted data grade)).comp
      (annularDataCut_tendsto lower (annularWeightedData lower angular cell inserted data grade))
  have same := annularSolutionNaturalPTrace_weighted_identity parameters lower length positive bounded lengthPositive widthHalf widthLength angular cell inserted endpoint data grade traceGrade
  exact (congrArg (fun value : AnnularBoundary => Tendsto
    (fun support : Finset HighAnnularMode => annularSolutionNaturalPTrace parameters lower length positive bounded lengthPositive widthHalf widthLength endpoint
      (annularDataCut lower (support : Set HighAnnularMode) (annularWeightedData lower angular cell inserted data grade))) atTop (𝓝 value)) same).mpr convergence

end Consumer
end Grad.AnnularFluxTrace
