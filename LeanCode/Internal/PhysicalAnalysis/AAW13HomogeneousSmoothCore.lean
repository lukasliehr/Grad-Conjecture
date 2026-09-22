import AAW12FiniteSolutionSupport

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

abbrev AnnularBulkTriple (lower : ℝ) := AnnularBulk lower × (AnnularBulk lower × AnnularBulk lower)
abbrev AnnularSmoothBulkTripleCore := AnnularSmoothBulkCore × (AnnularSmoothBulkCore × AnnularSmoothBulkCore)

def annularHomogeneousData (lower : ℝ) : AnnularBulkTriple lower →L[ℂ] (AnnularForcing lower × AnnularBoundary) where
  toFun bulk := ((bulk.1, (bulk.2.1, (bulk.2.2, 0))), 0)
  map_add' := by
    rintro ⟨a, b, c⟩ ⟨d, e, f⟩
    simp only [Prod.mk_add_mk, add_zero]
  map_smul' := by
    rintro scalar ⟨a, b, c⟩
    simp only [RingHom.id_apply, Prod.smul_mk, smul_zero]
  cont := by fun_prop

def annularFiniteBulkTriple (lower : ℝ) : AnnularSmoothBulkTripleCore →ₗ[ℝ] AnnularBulkTriple lower :=
  (annularFiniteSmoothBulk lower).prodMap ((annularFiniteSmoothBulk lower).prodMap (annularFiniteSmoothBulk lower))

def annularHomogeneousSmoothCore (core : AnnularSmoothBulkTripleCore) : AnnularSmoothDataCore :=
  ((core.1, (core.2.1, (core.2.2, 0))), 0)

theorem annularHomogeneousSmoothCore_data (lower : ℝ) (core : AnnularSmoothBulkTripleCore) :
    annularFiniteSmoothData lower (annularHomogeneousSmoothCore core) =
      annularHomogeneousData lower (annularFiniteBulkTriple lower core) := by
  change ((annularFiniteSmoothBulk lower core.1,
    (annularFiniteSmoothBulk lower core.2.1, (annularFiniteSmoothBulk lower core.2.2, annularFiniteBoundary 0))),
      annularFiniteBoundary 0) = _
  rw [map_zero]
  rfl

theorem annularGradedHomogeneousSmoothCore_boundary (lower : ℝ) (angular cell inserted : ℕ)
    (core : AnnularSmoothBulkTripleCore) :
    (annularGradedSmoothData lower angular cell inserted (annularHomogeneousSmoothCore core)).1.2.2.2 = 0 ∧
    (annularGradedSmoothData lower angular cell inserted (annularHomogeneousSmoothCore core)).2 = 0 := by
  constructor <;> change annularLpDecode angular cell inserted (annularFiniteBoundary 0) = 0
  all_goals rw [map_zero, map_zero]

/-- Boundary approximants stay identically zero. This gives full norm
density for the homogeneous solved graph with no endpoint correction. -/
theorem annularHomogeneousGraph_smooth_closure (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (angular cell inserted : ℕ) (bulk : AnnularBulkTriple lower) :
    annularFullGraphObservation parameters lower length positive bounded lengthPositive widthHalf widthLength
        (annularHomogeneousData lower bulk) ∈
      closure (Set.range (fun core : AnnularSmoothBulkTripleCore =>
        annularFullGraphObservation parameters lower length positive bounded lengthPositive widthHalf widthLength
          (annularWeightedData lower angular cell inserted
            (annularGradedSmoothData lower angular cell inserted (annularHomogeneousSmoothCore core))
            (annularGradedSmoothData_hasGrade lower angular cell inserted (annularHomogeneousSmoothCore core))))) := by
  simp only [annularGradedSmoothData_weighted, annularHomogeneousSmoothCore_data]
  have dense : DenseRange (annularFiniteBulkTriple lower) :=
    (annularFiniteSmoothBulk_denseRange lower positive).prodMap
      ((annularFiniteSmoothBulk_denseRange lower positive).prodMap (annularFiniteSmoothBulk_denseRange lower positive))
  apply isClosed_property dense
    (isClosed_closure.preimage
      ((annularFullGraphObservation parameters lower length positive bounded lengthPositive widthHalf widthLength).continuous.comp
        (annularHomogeneousData lower).continuous)) _ bulk
  intro core
  exact subset_closure ⟨core, rfl⟩

end Grad.AnnularRegularity
