import AAV11ActualGraphIsomorphism

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularConverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.GaugeCoefficients.Physical.WeightedTrace

section Consumer
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem annularWeakGraph_existsUnique (source : AnnularForcing lower) (innerValue : AnnularBoundary) :
    ∃! data : annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength,
      data.val.2 = source ∧
      annularEnergyTrace lower length positive bounded lengthPositive 0 data.val.1 = innerValue ∧
      annularDataFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength 1 data = -source.2.2.2 := by
  refine ⟨annularSolvedDataGraph parameters lower length positive bounded lengthPositive widthHalf widthLength (source, innerValue),
    ⟨rfl, annularVariationalSolution_inner parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue,
      annularSolvedData_outer parameters lower length positive bounded lengthPositive widthHalf widthLength (source, innerValue)⟩, ?_⟩
  intro candidate laws
  have outer : annularDataFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength 1 candidate =
      -candidate.val.2.2.2.2 := laws.2.2.trans (congrArg (fun data : AnnularForcing lower => -data.2.2.2) laws.1).symm
  have same := annularDataGraph_unique parameters lower length positive bounded lengthPositive widthHalf widthLength candidate innerValue laws.2.1 outer
  apply Subtype.ext
  apply Prod.ext
  · exact same.trans (congrArg (fun forcing : AnnularForcing lower =>
      annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength forcing innerValue) laws.1)
  · exact laws.1

/-- The original separate physical norm estimate now applies to EVERY weak
graph solution, by the proved converse. -/
theorem annularDataGraph_physical_bound
    (data : annularFluxDataGraph parameters lower length positive lengthPositive widthHalf widthLength)
    (innerValue : AnnularBoundary)
    (innerLaw : annularEnergyTrace lower length positive bounded lengthPositive 0 data.val.1 = innerValue)
    (outerLaw : annularDataFluxTrace parameters lower length positive bounded lengthPositive widthHalf widthLength 1 data =
      -data.val.2.2.2.2) :
    ‖data.val.1‖ ≤ annularInnerLiftConstant lower length * ‖innerValue‖ +
      (4 / 3 : ℝ) * (3 * ‖data.val.2.1‖ + ‖data.val.2.2.1‖ + ‖data.val.2.2.2.1‖ +
        annularTraceConstant lower length * ‖data.val.2.2.2.2‖ +
        4 * annularInnerLiftConstant lower length * ‖innerValue‖) :=
  (congrArg norm (annularDataGraph_unique parameters lower length positive bounded lengthPositive widthHalf widthLength
    data innerValue innerLaw outerLaw)).trans_le
    (annularVariationalSolution_bound parameters lower length positive bounded lengthPositive widthHalf widthLength data.val.2 innerValue)

/-- Both inverse laws on the independently defined complete graph. -/
theorem annularWeakGraph_isomorphism_consumer
    (data : AnnularForcing lower × AnnularBoundary)
    (graph : annularBoundaryFluxGraph parameters lower length positive bounded lengthPositive widthHalf widthLength) :
    annularBoundaryGraphEquivalence parameters lower length positive bounded lengthPositive widthHalf widthLength
      ((annularBoundaryGraphEquivalence parameters lower length positive bounded lengthPositive widthHalf widthLength).symm data) = data ∧
    (annularBoundaryGraphEquivalence parameters lower length positive bounded lengthPositive widthHalf widthLength).symm
      (annularBoundaryGraphEquivalence parameters lower length positive bounded lengthPositive widthHalf widthLength graph) = graph :=
  ⟨(annularBoundaryGraphEquivalence parameters lower length positive bounded lengthPositive widthHalf widthLength).apply_symm_apply data,
    (annularBoundaryGraphEquivalence parameters lower length positive bounded lengthPositive widthHalf widthLength).symm_apply_apply graph⟩

end Consumer
end Grad.AnnularConverse
