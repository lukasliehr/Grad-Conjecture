import AAW13HomogeneousSmoothCore
import AAV11ActualGraphIsomorphism

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades Grad.AnnularConverse
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Pure source-density transport, with the observation space left abstract. -/
theorem annularHomogeneous_observation_closure (lower : ℝ) (positive : 0 < lower)
    {E : Type*} [TopologicalSpace E]
    (observe : (AnnularForcing lower × AnnularBoundary) → E) (continuous : Continuous observe)
    (bulk : AnnularBulkTriple lower) :
    observe (annularHomogeneousData lower bulk) ∈
      closure (Set.range (fun core : AnnularSmoothBulkTripleCore =>
        observe (annularFiniteSmoothData lower (annularHomogeneousSmoothCore core)))) := by
  simp only [annularHomogeneousSmoothCore_data]
  have dense : DenseRange (annularFiniteBulkTriple lower) :=
    (annularFiniteSmoothBulk_denseRange lower positive).prodMap
      ((annularFiniteSmoothBulk_denseRange lower positive).prodMap (annularFiniteSmoothBulk_denseRange lower positive))
  apply isClosed_property dense
    (isClosed_closure.preimage (continuous.comp (annularHomogeneousData lower).continuous)) _ bulk
  intro core
  exact subset_closure ⟨core, rfl⟩

section Actual
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- Actual smooth data mapped by the same inverse into the independently
defined weak graph with the original natural boundary condition. -/
def annularFiniteSmoothGraph (core : AnnularSmoothDataCore) :
    annularBoundaryFluxGraph parameters lower length positive bounded lengthPositive widthHalf widthLength :=
  (annularBoundaryGraphEquivalence parameters lower length positive bounded lengthPositive widthHalf widthLength).symm
    (annularFiniteSmoothData lower core)

theorem annularFiniteSmoothGraph_state (core : AnnularSmoothDataCore) :
    (annularFiniteSmoothGraph parameters lower length positive bounded lengthPositive widthHalf widthLength core).val.val.1 =
      annularVariationalInverse parameters lower length positive bounded lengthPositive widthHalf widthLength
        (annularFiniteSmoothData lower core) := rfl

/-- The actual finite-mode smooth inverses are dense in the original
complete boundary weak graph, using the proved graph converse. -/
theorem annularFiniteSmoothGraph_denseRange :
    DenseRange (annularFiniteSmoothGraph parameters lower length positive bounded lengthPositive widthHalf widthLength) :=
  (annularBoundaryGraphEquivalence parameters lower length positive bounded lengthPositive widthHalf widthLength).symm.surjective.denseRange.comp
    (annularFiniteSmoothData_denseRange lower positive)
    (annularBoundaryGraphEquivalence parameters lower length positive bounded lengthPositive widthHalf widthLength).symm.continuous

/-- Homogeneous boundary graph elements have smooth approximants whose
inner and outer data remain identically zero. -/
theorem annularHomogeneousBoundaryGraph_smooth_closure
    (graph : annularBoundaryFluxGraph parameters lower length positive bounded lengthPositive widthHalf widthLength)
    (outerZero : graph.val.val.2.2.2.2 = 0)
    (innerZero : annularEnergyTrace lower length positive bounded lengthPositive 0 graph.val.val.1 = 0) :
    graph ∈ closure (Set.range (fun core : AnnularSmoothBulkTripleCore =>
      annularFiniteSmoothGraph parameters lower length positive bounded lengthPositive widthHalf widthLength
        (annularHomogeneousSmoothCore core))) := by
  let equivalence := annularBoundaryGraphEquivalence parameters lower length positive bounded lengthPositive widthHalf widthLength
  let bulk : AnnularBulkTriple lower := (graph.val.val.2.1, (graph.val.val.2.2.1, graph.val.val.2.2.2.1))
  have dataLaw : annularHomogeneousData lower bulk = equivalence graph := by
    change ((graph.val.val.2.1, (graph.val.val.2.2.1, (graph.val.val.2.2.2.1, 0))), 0) =
      (graph.val.val.2, annularEnergyTrace lower length positive bounded lengthPositive 0 graph.val.val.1)
    exact congrArg₂ (fun source : AnnularForcing lower => fun boundary : AnnularBoundary => (source, boundary))
      (congrArg (fun boundary : AnnularBoundary =>
        (graph.val.val.2.1, (graph.val.val.2.2.1, (graph.val.val.2.2.2.1, boundary)))) outerZero.symm)
      innerZero.symm
  have pointLaw : equivalence.symm (annularHomogeneousData lower bulk) = graph :=
    (congrArg equivalence.symm dataLaw).trans (equivalence.symm_apply_apply graph)
  have member := annularHomogeneous_observation_closure lower positive
    equivalence.symm equivalence.symm.continuous bulk
  exact (congrArg (fun value => value ∈ closure (Set.range (fun core : AnnularSmoothBulkTripleCore =>
    equivalence.symm (annularFiniteSmoothData lower (annularHomogeneousSmoothCore core))))) pointLaw).mp member

end Actual
end Grad.AnnularRegularity
