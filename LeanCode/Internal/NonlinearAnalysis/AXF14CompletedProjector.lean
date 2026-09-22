import AXF13FiniteCells

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.CartesianState Grad.RealFixedRanges Grad.ChartAxisProjections Grad.ConstrainedGrades

def flatBoundConstant (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) : ℝ :=
  Classical.choose (realFlatSourceProjection_bound parameters grade large)

theorem flatBoundConstant_nonneg (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    0 ≤ flatBoundConstant parameters grade large :=
  (Classical.choose_spec (realFlatSourceProjection_bound parameters grade large)).1

theorem realFlatSourceProjection_norm_le (parameters : PhaseParameters) (grade : ℕ)
    (large : 3 ≤ grade) (source : sourceSmoothRange parameters) :
    ‖sourceSmoothEmbedding parameters grade large (realFlatSourceProjection source)‖ ≤
      flatBoundConstant parameters grade large * ‖sourceSmoothEmbedding parameters grade large source‖ :=
  (Classical.choose_spec (realFlatSourceProjection_bound parameters grade large)).2 source

def flatGradeCoreLinear (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    SourceGradeCore parameters grade large →ₗ[ℝ] sourceRange parameters grade large :=
  (sourceSmoothEmbedding parameters grade large).comp
    (realFlatSourceProjection.comp NormedCoreCopy.toCoreLinear)

def flatGradeCoreContinuous (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    SourceGradeCore parameters grade large →L[ℝ] sourceRange parameters grade large :=
  (flatGradeCoreLinear parameters grade large).mkContinuous
    (flatBoundConstant parameters grade large)
    (fun source => realFlatSourceProjection_norm_le parameters grade large source.toCore)

/-- The fixed projector extends on the unchanged complete real source space. -/
def completedFlatSourceProjection (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    sourceRange parameters grade large →L[ℝ] sourceRange parameters grade large :=
  (flatGradeCoreContinuous parameters grade large).extend
    (sourceGradeEmbedding parameters grade large).toContinuousLinearMap

theorem completedFlatSourceProjection_core (parameters : PhaseParameters) (grade : ℕ)
    (large : 3 ≤ grade) (source : sourceSmoothRange parameters) :
    completedFlatSourceProjection parameters grade large
      (sourceSmoothEmbedding parameters grade large source) =
        sourceSmoothEmbedding parameters grade large (realFlatSourceProjection source) := by
  exact Grad.ConstrainedTransfer.denseIsometryExtension_core
    (flatGradeCoreContinuous parameters grade large)
    (sourceGradeEmbedding parameters grade large)
    (sourceGradeEmbedding_denseRange parameters grade large)
    (⟨source⟩ : SourceGradeCore parameters grade large)

theorem completedFlatSourceProjection_bound (parameters : PhaseParameters) (grade : ℕ)
    (large : 3 ≤ grade) (source : sourceRange parameters grade large) :
    ‖completedFlatSourceProjection parameters grade large source‖ ≤
      flatBoundConstant parameters grade large * ‖source‖ := by
  apply isClosed_property (sourceSmoothEmbedding_denseRange parameters grade large)
    (isClosed_le (completedFlatSourceProjection parameters grade large).continuous.norm
      (continuous_const.mul continuous_norm)) _ source
  intro core
  rw [completedFlatSourceProjection_core]
  exact realFlatSourceProjection_norm_le parameters grade large core

theorem completedFlatSourceProjection_idempotent (parameters : PhaseParameters) (grade : ℕ)
    (large : 3 ≤ grade) (source : sourceRange parameters grade large) :
    completedFlatSourceProjection parameters grade large
      (completedFlatSourceProjection parameters grade large source) =
        completedFlatSourceProjection parameters grade large source := by
  apply isClosed_property (sourceSmoothEmbedding_denseRange parameters grade large)
    (isClosed_eq
      ((completedFlatSourceProjection parameters grade large).continuous.comp
        (completedFlatSourceProjection parameters grade large).continuous)
      (completedFlatSourceProjection parameters grade large).continuous) _ source
  intro core
  simp only [Function.comp_apply]
  rw [completedFlatSourceProjection_core, completedFlatSourceProjection_core,
    realFlatSourceProjection_idempotent]

theorem completedFlatSourceProjection_unique (parameters : PhaseParameters) (grade : ℕ)
    (large : 3 ≤ grade)
    (other : sourceRange parameters grade large →L[ℝ] sourceRange parameters grade large)
    (law : ∀ source, other (sourceSmoothEmbedding parameters grade large source) =
      sourceSmoothEmbedding parameters grade large (realFlatSourceProjection source)) :
    other = completedFlatSourceProjection parameters grade large := by
  apply ContinuousLinearMap.ext
  exact congrFun ((sourceSmoothEmbedding_denseRange parameters grade large).equalizer
    other.continuous (completedFlatSourceProjection parameters grade large).continuous
    (funext fun source => (law source).trans
      (completedFlatSourceProjection_core parameters grade large source).symm))

theorem completedFlatSourceProjection_grade (parameters : PhaseParameters)
    {lower upper : ℕ} (large : 3 ≤ lower) (ordered : lower ≤ upper)
    (source : sourceRange parameters upper (large.trans ordered)) :
    sourceLowering parameters large ordered
      (completedFlatSourceProjection parameters upper (large.trans ordered) source) =
        completedFlatSourceProjection parameters lower large
          (sourceLowering parameters large ordered source) := by
  apply isClosed_property (sourceSmoothEmbedding_denseRange parameters upper (large.trans ordered))
    (isClosed_eq
      ((sourceLowering parameters large ordered).continuous.comp
        (completedFlatSourceProjection parameters upper (large.trans ordered)).continuous)
      ((completedFlatSourceProjection parameters lower large).continuous.comp
        (sourceLowering parameters large ordered).continuous)) _ source
  intro core
  simp only [Function.comp_apply]
  rw [completedFlatSourceProjection_core, sourceLowering_core, sourceLowering_core,
    completedFlatSourceProjection_core]

end Grad.FlatSourceProjection
