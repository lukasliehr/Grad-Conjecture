import AXF14CompletedProjector

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.CartesianState Grad.RealFixedRanges Grad.ChartAxisProjections

/-- Closed fixed range inside the unchanged original complete real Y grade. -/
def flatSourceRange (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    Submodule ℝ (sourceRange parameters grade large) :=
  (completedFlatSourceProjection parameters grade large -
    ContinuousLinearMap.id ℝ (sourceRange parameters grade large)).ker

theorem mem_flatSourceRange (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade)
    (source : sourceRange parameters grade large) :
    source ∈ flatSourceRange parameters grade large ↔
      completedFlatSourceProjection parameters grade large source = source := by
  change (_ - source = 0) ↔ _
  exact sub_eq_zero

theorem flatSourceRange_closed (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    IsClosed (flatSourceRange parameters grade large : Set (sourceRange parameters grade large)) :=
  (completedFlatSourceProjection parameters grade large -
    ContinuousLinearMap.id ℝ (sourceRange parameters grade large)).isClosed_ker

instance flatSourceRange_complete (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    CompleteSpace (flatSourceRange parameters grade large) :=
  (flatSourceRange_closed parameters grade large).completeSpace_coe

def flatSourceRetraction (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    sourceRange parameters grade large →L[ℝ] flatSourceRange parameters grade large :=
  (completedFlatSourceProjection parameters grade large).codRestrict
    (flatSourceRange parameters grade large) (fun source =>
      (mem_flatSourceRange parameters grade large _).mpr
        (completedFlatSourceProjection_idempotent parameters grade large source))

theorem flatSourceRetraction_fixes (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade)
    (source : flatSourceRange parameters grade large) :
    flatSourceRetraction parameters grade large source.val = source :=
  Subtype.ext ((mem_flatSourceRange parameters grade large source.val).mp source.property)

theorem flatSourceRetraction_surjective (parameters : PhaseParameters) (grade : ℕ)
    (large : 3 ≤ grade) : Function.Surjective (flatSourceRetraction parameters grade large) :=
  fun source => ⟨source.val, flatSourceRetraction_fixes parameters grade large source⟩

def flatSmoothEmbedding (parameters : PhaseParameters) (cellLength : ℝ) (positive : 0 < cellLength)
    (grade : ℕ) (large : 3 ≤ grade) :
    LinearMap.ker (realExtraction parameters cellLength) →ₗ[ℝ] flatSourceRange parameters grade large :=
  ((sourceSmoothEmbedding parameters grade large).comp
    (LinearMap.ker (realExtraction parameters cellLength)).subtype).codRestrict
      (flatSourceRange parameters grade large) (fun source => by
        rw [mem_flatSourceRange]
        change completedFlatSourceProjection parameters grade large
          (sourceSmoothEmbedding parameters grade large source.val) = _
        rw [completedFlatSourceProjection_core,
          realFlatSourceProjection_fixes cellLength positive source.val source.property]
        rfl)

theorem flatSmoothEmbedding_injective (parameters : PhaseParameters)
    (cellLength : ℝ) (positive : 0 < cellLength) (grade : ℕ) (large : 3 ≤ grade) :
    Function.Injective (flatSmoothEmbedding parameters cellLength positive grade large) := by
  intro first second equality
  apply Subtype.ext
  apply sourceSmoothEmbedding_injective parameters grade large
  exact congrArg Subtype.val equality

/-- Exact smooth ker J is dense in the original-norm complete fixed range. -/
theorem flatSmoothEmbedding_denseRange (parameters : PhaseParameters)
    (cellLength : ℝ) (positive : 0 < cellLength) (grade : ℕ) (large : 3 ≤ grade) :
    DenseRange (flatSmoothEmbedding parameters cellLength positive grade large) := by
  have dense := (flatSourceRetraction_surjective parameters grade large).denseRange.comp
    (sourceSmoothEmbedding_denseRange parameters grade large)
    (flatSourceRetraction parameters grade large).continuous
  apply dense.mono
  rintro _ ⟨source, rfl⟩
  refine ⟨⟨realFlatSourceProjection source,
    realFlatSourceProjection_mem cellLength positive source⟩, ?_⟩
  apply Subtype.ext
  exact (completedFlatSourceProjection_core parameters grade large source).symm

theorem flatSmoothEmbedding_original_norm (parameters : PhaseParameters)
    (cellLength : ℝ) (positive : 0 < cellLength) (grade : ℕ) (large : 3 ≤ grade)
    (source : LinearMap.ker (realExtraction parameters cellLength)) :
    ‖flatSmoothEmbedding parameters cellLength positive grade large source‖ =
      Grad.QuotientProjection.quotientNorm parameters grade source.val.val := rfl

end Grad.FlatSourceProjection
