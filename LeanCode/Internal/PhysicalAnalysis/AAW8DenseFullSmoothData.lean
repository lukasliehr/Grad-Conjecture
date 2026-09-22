import AAW7DenseSmoothBulkData
import AAQ19ExactSharpTraceConsumer

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

abbrev AnnularSmoothBulkCore := HighAnnularMode →₀ SmoothRadialCore 1
abbrev AnnularFiniteBoundaryCore := HighAnnularMode →₀ ComplexEuclidean 1
abbrev AnnularSmoothDataCore := (AnnularSmoothBulkCore ×
  (AnnularSmoothBulkCore × (AnnularSmoothBulkCore × AnnularFiniteBoundaryCore))) × AnnularFiniteBoundaryCore

def annularFiniteBoundary : AnnularFiniteBoundaryCore →ₗ[ℝ] AnnularBoundary :=
  Finsupp.lsum ℝ (fun mode =>
    (lp.singleContinuousLinearMap ℝ (fun _ : HighAnnularMode => ComplexEuclidean 1) 2 mode).toLinearMap)

theorem annularFiniteBoundary_single (mode : HighAnnularMode) (value : ComplexEuclidean 1) :
    annularFiniteBoundary (Finsupp.single mode value) = lp.single 2 mode value := by
  rw [annularFiniteBoundary, Finsupp.lsum_single]
  rfl

theorem annularFiniteBoundary_apply (core : AnnularFiniteBoundaryCore) (mode : HighAnnularMode) :
    annularFiniteBoundary core mode = core mode := by
  classical
  rw [annularFiniteBoundary, Finsupp.lsum_apply, Finsupp.sum, lp.coeFn_sum, Finset.sum_apply]
  change (∑ other ∈ core.support, (lp.single 2 other (core other) : AnnularBoundary) mode) = _
  simp only [lp.single_apply, Pi.single_apply]
  rw [Finset.sum_eq_single mode]
  · simp only [ite_true]
  · intro other _ different
    exact if_neg (Ne.symm different)
  · intro missing
    rw [Finsupp.notMem_support_iff.mp missing]
    simp

theorem annularFiniteBoundary_denseRange : DenseRange annularFiniteBoundary := by
  let subspace := (LinearMap.range annularFiniteBoundary).topologicalClosure
  have singleMember (mode : HighAnnularMode) (value : ComplexEuclidean 1) :
      (lp.single 2 mode value : AnnularBoundary) ∈ subspace := by
    apply Submodule.le_topologicalClosure
    exact ⟨Finsupp.single mode value, annularFiniteBoundary_single mode value⟩
  have closureTop : subspace = ⊤ := by
    apply top_unique
    intro field _
    have convergence : HasSum (fun mode : HighAnnularMode => (lp.single 2 mode (field mode) : AnnularBoundary)) field :=
      lp.hasSum_single (by norm_num) field
    apply (LinearMap.range annularFiniteBoundary).isClosed_topologicalClosure.mem_of_tendsto convergence
    exact Filter.Eventually.of_forall (fun support => subspace.sum_mem (fun mode _ => singleMember mode (field mode)))
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr closureTop

/-- All three true bulk coordinates and both true boundary coordinates. -/
def annularFiniteSmoothData (lower : ℝ) : AnnularSmoothDataCore →ₗ[ℝ] (AnnularForcing lower × AnnularBoundary) :=
  ((annularFiniteSmoothBulk lower).prodMap
    ((annularFiniteSmoothBulk lower).prodMap ((annularFiniteSmoothBulk lower).prodMap annularFiniteBoundary))).prodMap
      annularFiniteBoundary

theorem annularFiniteSmoothData_denseRange (lower : ℝ) (positive : 0 < lower) :
    DenseRange (annularFiniteSmoothData lower) :=
  ((annularFiniteSmoothBulk_denseRange lower positive).prodMap
    ((annularFiniteSmoothBulk_denseRange lower positive).prodMap
      ((annularFiniteSmoothBulk_denseRange lower positive).prodMap annularFiniteBoundary_denseRange))).prodMap
        annularFiniteBoundary_denseRange

/-- Every approximating datum produces the proved smooth actual inverse. -/
theorem annularFiniteSmoothData_solution (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (core : AnnularSmoothDataCore) (mode : HighAnnularMode) :
    let data := annularFiniteSmoothData lower core
    ContDiffOn ℝ ∞ (annularSolutionXiCurve parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode) (Icc lower 1) ∧
    ContDiffOn ℝ ∞ (annularSolutionQCurve parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode) (Icc lower 1) ∧
    ContDiffOn ℝ ∞ (annularSolutionPCurve parameters lower length positive bounded lengthPositive widthHalf widthLength data.1 data.2 mode) (Icc lower 1) := by
  dsimp only
  apply annularSameSolution_smooth parameters lower length positive bounded lengthPositive widthHalf widthLength _ _ mode
    (annularSmoothPhysicalCurve parameters mode (core.1.1 mode))
    (annularSmoothPhysicalCurve parameters mode (core.1.2.1 mode))
    (annularSmoothPhysicalCurve parameters mode (core.1.2.2.1 mode))
    (annularSmoothPhysicalCurve_smooth parameters mode (core.1.1 mode)).contDiffOn
    (annularSmoothPhysicalCurve_smooth parameters mode (core.1.2.1 mode)).contDiffOn
    (annularSmoothPhysicalCurve_smooth parameters mode (core.1.2.2.1 mode)).contDiffOn
  all_goals
    change annularDecodeMode parameters lower positive mode (annularFiniteSmoothBulk lower _ mode) =ᵐ[_] _
    rw [annularFiniteSmoothBulk_apply]
    exact annularSmoothBulkMode_physical parameters lower positive mode _

end Grad.AnnularRegularity
