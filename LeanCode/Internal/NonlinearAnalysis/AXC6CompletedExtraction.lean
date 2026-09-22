import AXC5DataLinear

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.ChartAxisSplit

open Grad.CartesianState Grad.AxisSplit Grad.RealFixedRanges Grad.QuotientProjection

theorem extractionLarge (grade : ℕ) : 3 ≤ grade + 3 := by omega

def extractionGradeCoreLinear (parameters : PhaseParameters) (cellLength : ℝ) (grade : ℕ) :
    SourceGradeCore parameters (grade + 3) (extractionLarge grade) →ₗ[ℝ]
      AxisDataGrade parameters grade :=
  (((axisDataEmbedding parameters grade).comp (extractionLinear parameters cellLength)).restrictScalars ℝ).comp
    ((sourceSmoothRange parameters).subtype.comp NormedCoreCopy.toCoreLinear)

def extractionGradeCore (parameters : PhaseParameters) (cellLength : ℝ) (grade : ℕ) :
    SourceGradeCore parameters (grade + 3) (extractionLarge grade) →L[ℝ]
      AxisDataGrade parameters grade :=
  (extractionGradeCoreLinear parameters cellLength grade).mkContinuous
    (4 * extractionBoundConstant cellLength) (fun source =>
      extraction_exact_norm_bound parameters cellLength grade source.toCore.val)

/-- AL10/AL13 on the actual completed real source space, without changing
the fourfold Hilbert source norm or the shifted sum norm of axis data. -/
def completedExtraction (parameters : PhaseParameters) (cellLength : ℝ) (grade : ℕ) :
    sourceRange parameters (grade + 3) (extractionLarge grade) →L[ℝ]
      AxisDataGrade parameters grade :=
  (extractionGradeCore parameters cellLength grade).extend
    (sourceGradeEmbedding parameters (grade + 3) (extractionLarge grade)).toContinuousLinearMap

theorem completedExtraction_core (parameters : PhaseParameters) (cellLength : ℝ) (grade : ℕ)
    (source : sourceSmoothRange parameters) :
    completedExtraction parameters cellLength grade
      (sourceSmoothEmbedding parameters (grade + 3) (extractionLarge grade) source) =
        axisDataEmbedding parameters grade (extractionData cellLength source.val) := by
  have step := Grad.ConstrainedTransfer.denseIsometryExtension_core
    (extractionGradeCore parameters cellLength grade)
    (sourceGradeEmbedding parameters (grade + 3) (extractionLarge grade))
    (sourceGradeEmbedding_denseRange parameters (grade + 3) (extractionLarge grade))
    (⟨source⟩ : SourceGradeCore parameters (grade + 3) (extractionLarge grade))
  exact step

theorem completedExtraction_bound (parameters : PhaseParameters) (cellLength : ℝ) (grade : ℕ)
    (source : sourceRange parameters (grade + 3) (extractionLarge grade)) :
    ‖completedExtraction parameters cellLength grade source‖ ≤
      (4 * extractionBoundConstant cellLength) * ‖source‖ := by
  apply isClosed_property
    (sourceSmoothEmbedding_denseRange parameters (grade + 3) (extractionLarge grade))
    (isClosed_le (completedExtraction parameters cellLength grade).continuous.norm
      (continuous_const.mul continuous_norm)) _ source
  intro core
  rw [completedExtraction_core]
  exact extraction_exact_norm_bound parameters cellLength grade core.val

theorem completedExtraction_unique (parameters : PhaseParameters) (cellLength : ℝ) (grade : ℕ)
    (other : sourceRange parameters (grade + 3) (extractionLarge grade) →L[ℝ]
      AxisDataGrade parameters grade)
    (coreLaw : ∀ source : sourceSmoothRange parameters,
      other (sourceSmoothEmbedding parameters (grade + 3) (extractionLarge grade) source) =
        axisDataEmbedding parameters grade (extractionData cellLength source.val)) :
    other = completedExtraction parameters cellLength grade := by
  apply ContinuousLinearMap.ext
  exact congrFun ((sourceSmoothEmbedding_denseRange parameters (grade + 3) (extractionLarge grade)).equalizer
    other.continuous (completedExtraction parameters cellLength grade).continuous
    (funext fun source => (coreLaw source).trans (completedExtraction_core parameters cellLength grade source).symm))

end Grad.ChartAxisSplit
