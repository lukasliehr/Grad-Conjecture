import AAW9WeightedSmoothData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- A continuous observation of the full original data is approximated by
finite-mode smooth data in its actual norm topology. -/
theorem annularSmoothData_observation_closure (lower : ℝ) (positive : 0 < lower)
    {E : Type*} [TopologicalSpace E]
    (observe : (AnnularForcing lower × AnnularBoundary) → E) (continuous : Continuous observe)
    (data : AnnularForcing lower × AnnularBoundary) :
    observe data ∈ closure (Set.range (fun core : AnnularSmoothDataCore => observe (annularFiniteSmoothData lower core))) := by
  apply isClosed_property (annularFiniteSmoothData_denseRange lower positive)
    (isClosed_closure.preimage continuous) _ data
  intro core
  exact subset_closure ⟨core, rfl⟩

section Actual
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- The observation keeps all five source/boundary coordinates, the actual
energy solution, and BOTH coordinates of its genuine weak q graph. -/
def annularFullGraphObservation : (AnnularForcing lower × AnnularBoundary) →L[ℂ]
    ((AnnularForcing lower × AnnularBoundary) ×
      (annularEnergySpace lower length positive × annularFluxWeakGraph lower positive)) :=
  (ContinuousLinearMap.id ℂ _).prod
    ((annularVariationalInverse parameters lower length positive bounded lengthPositive widthHalf widthLength).prod
      (annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength))

/-- Full norm approximation of the actual solved graph. None of the weak
q slope or boundary coordinates is discarded in this closure statement. -/
theorem annularFullGraph_smooth_closure (data : AnnularForcing lower × AnnularBoundary) :
    annularFullGraphObservation parameters lower length positive bounded lengthPositive widthHalf widthLength data ∈
      closure (Set.range (fun core : AnnularSmoothDataCore =>
        annularFullGraphObservation parameters lower length positive bounded lengthPositive widthHalf widthLength
          (annularFiniteSmoothData lower core))) :=
  annularSmoothData_observation_closure lower positive _
    (annularFullGraphObservation parameters lower length positive bounded lengthPositive widthHalf widthLength).continuous data

/-- At every supplied grade, the normalized full graph is the same actual
inverse of the normalized weighted data, by the proved commutation laws. -/
theorem annularFullGraph_weighted_identity (angular cell inserted : ℕ)
    (data : AnnularForcing lower × AnnularBoundary) (grade : HasAnnularDataGrade lower angular cell inserted data) :
    annularFullGraphObservation parameters lower length positive bounded lengthPositive widthHalf widthLength
        (annularWeightedData lower angular cell inserted data grade) =
      (annularWeightedData lower angular cell inserted data grade,
        (annularWeightedEnergy lower length positive angular cell inserted
          (annularVariationalInverse parameters lower length positive bounded lengthPositive widthHalf widthLength data)
          (annularInverse_hasGrade parameters lower length positive bounded lengthPositive widthHalf widthLength angular cell inserted data grade),
        annularFluxGraphWeighted lower positive angular cell inserted
          (annularSolvedFlux parameters lower length positive bounded lengthPositive widthHalf widthLength data)
          (annularSolvedFlux_hasGrade parameters lower length positive bounded lengthPositive widthHalf widthLength angular cell inserted data grade))) := by
  refine Prod.ext ?_ ?_
  · rfl
  · apply Prod.ext
    · exact (annularInverse_weighted_identity parameters lower length positive bounded lengthPositive widthHalf widthLength angular cell inserted data grade
        (annularInverse_hasGrade parameters lower length positive bounded lengthPositive widthHalf widthLength angular cell inserted data grade)).symm
    · exact (annularSolvedFlux_weighted_identity parameters lower length positive bounded lengthPositive widthHalf widthLength angular cell inserted data grade
        (annularSolvedFlux_hasGrade parameters lower length positive bounded lengthPositive widthHalf widthLength angular cell inserted data grade)).symm

/-- Smooth original-width inverses approximate every graded solved graph in
its full weighted source/energy/weak-flux norm. The approximants are exactly
AAW9's graded smooth data; no auxiliary completion replaces that graph. -/
theorem annularGradedGraph_smooth_closure (angular cell inserted : ℕ)
    (data : AnnularForcing lower × AnnularBoundary) (grade : HasAnnularDataGrade lower angular cell inserted data) :
    annularFullGraphObservation parameters lower length positive bounded lengthPositive widthHalf widthLength
        (annularWeightedData lower angular cell inserted data grade) ∈
      closure (Set.range (fun core : AnnularSmoothDataCore =>
        annularFullGraphObservation parameters lower length positive bounded lengthPositive widthHalf widthLength
          (annularWeightedData lower angular cell inserted (annularGradedSmoothData lower angular cell inserted core)
            (annularGradedSmoothData_hasGrade lower angular cell inserted core)))) := by
  simp only [annularGradedSmoothData_weighted]
  exact annularFullGraph_smooth_closure parameters lower length positive bounded lengthPositive widthHalf widthLength _

end Actual
end Grad.AnnularRegularity
