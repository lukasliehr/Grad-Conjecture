import QP8Proof
import CQ1DenseExtension

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.QuotientProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.AxisCore

theorem quotientEta_injective (parameters : PhaseParameters) (grade : ℕ) :
    Function.Injective (quotientEta parameters grade) := by
  intro first second equality
  funext coordinate
  have components := congrArg (fun field : ZAmbient parameters grade => field coordinate) equality
  change aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) (first coordinate)) =
    aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) (second coordinate)) at components
  exact congrArg GradeCore.toCore ((aGradeEta parameters).injective components)

theorem quotientEta_denseRange (parameters : PhaseParameters) (grade : ℕ) :
    DenseRange (quotientEta parameters grade) := by
  apply (zEmbedding_denseRange parameters grade).mono
  rintro _ ⟨cores, rfl⟩
  refine ⟨fun coordinate => (cores coordinate).toCore, ?_⟩
  apply PiLp.ext
  intro coordinate
  change aGradeEta parameters (GradeCore.ofCoreLinear (cores coordinate).toCore) =
    aGradeEta parameters (cores coordinate)
  rw [GradeCore.ofCore_toCore]

/-- Immediate COR22 consumer: COR21 supplies an actual completed bounded
idempotent with the exact core equation and uniqueness. The additional real
involution/intertwining obligations of COR22 are not claimed here. -/
theorem completedQuotientProjection_exists (parameters : PhaseParameters)
    (grade : ℕ) (large : 3 ≤ grade) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∃ completed : ZAmbient parameters grade →L[ℂ] ZAmbient parameters grade,
      (∀ field, completed (quotientEta parameters grade field) =
        quotientEta parameters grade (quotientProjection parameters field)) ∧
      (∀ point, ‖completed point‖ ≤ constant * ‖point‖) ∧
      (∀ point, completed (completed point) = completed point) ∧
      (∀ other : ZAmbient parameters grade →L[ℂ] ZAmbient parameters grade,
        (∀ field, other (quotientEta parameters grade field) =
          quotientEta parameters grade (quotientProjection parameters field)) → other = completed) := by
  have result := actualSmoothQuotientProjection parameters
  obtain ⟨constant, positive, bound⟩ := result.2.2.2.1 grade large
  refine ⟨constant, positive, ?_⟩
  exact Grad.Cor18.dense_core_projection_extension
    (quotientEta parameters grade) (quotientEta_injective parameters grade)
    (quotientEta_denseRange parameters grade) (quotientProjection parameters)
    constant positive bound result.2.2.2.2.1

end Grad.QuotientProjection
