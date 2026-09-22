import AAW10SmoothGraphApproximation

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

open Grad.ActualBandCompletion

def annularSmoothDataSupport (core : AnnularSmoothDataCore) : Finset HighAnnularMode :=
  core.1.1.support ∪ core.1.2.1.support ∪ core.1.2.2.1.support ∪ core.1.2.2.2.support ∪ core.2.support

theorem annularFiniteSmoothBulk_cut (lower : ℝ) (core : AnnularSmoothBulkCore)
    (keep : Set HighAnnularMode) (contains : ∀ mode ∈ core.support, mode ∈ keep) :
    realLpDiagonal (fourierMask keep) 1 (by norm_num) (fourierMask_bound keep)
      (annularFiniteSmoothBulk lower core) = annularFiniteSmoothBulk lower core := by
  classical
  apply lp.ext
  funext mode
  rw [realLpDiagonal_apply, annularFiniteSmoothBulk_apply]
  by_cases member : mode ∈ keep
  · simp [fourierMask, member]
  · have missing : mode ∉ core.support := fun supported => member (contains mode supported)
    rw [Finsupp.notMem_support_iff.mp missing, map_zero, smul_zero]

theorem annularFiniteBoundary_cut (core : AnnularFiniteBoundaryCore)
    (keep : Set HighAnnularMode) (contains : ∀ mode ∈ core.support, mode ∈ keep) :
    realLpDiagonal (fourierMask keep) 1 (by norm_num) (fourierMask_bound keep)
      (annularFiniteBoundary core) = annularFiniteBoundary core := by
  classical
  apply lp.ext
  funext mode
  rw [realLpDiagonal_apply, annularFiniteBoundary_apply]
  by_cases member : mode ∈ keep
  · simp [fourierMask, member]
  · have missing : mode ∉ core.support := fun supported => member (contains mode supported)
    rw [Finsupp.notMem_support_iff.mp missing, smul_zero]

theorem annularFiniteSmoothData_cut (lower : ℝ) (core : AnnularSmoothDataCore) :
    annularDataCut lower (annularSmoothDataSupport core : Set HighAnnularMode) (annularFiniteSmoothData lower core) =
      annularFiniteSmoothData lower core := by
  classical
  apply Prod.ext
  · apply Prod.ext
    · exact annularFiniteSmoothBulk_cut lower core.1.1 _ (by
        intro mode member
        simp [annularSmoothDataSupport, member])
    · apply Prod.ext
      · exact annularFiniteSmoothBulk_cut lower core.1.2.1 _ (by
          intro mode member
          simp [annularSmoothDataSupport, member])
      · apply Prod.ext
        · exact annularFiniteSmoothBulk_cut lower core.1.2.2.1 _ (by
            intro mode member
            simp [annularSmoothDataSupport, member])
        · exact annularFiniteBoundary_cut core.1.2.2.2 _ (by
            intro mode member
            simp [annularSmoothDataSupport, member])
  · exact annularFiniteBoundary_cut core.2 _ (by
      intro mode member
      simp [annularSmoothDataSupport, member])

theorem annularGradedSmoothData_cut (lower : ℝ) (angular cell inserted : ℕ) (core : AnnularSmoothDataCore) :
    annularDataCut lower (annularSmoothDataSupport core : Set HighAnnularMode)
      (annularGradedSmoothData lower angular cell inserted core) = annularGradedSmoothData lower angular cell inserted core := by
  unfold annularGradedSmoothData
  rw [← annularDataDecode_cut, annularFiniteSmoothData_cut]

end Grad.AnnularRegularity
