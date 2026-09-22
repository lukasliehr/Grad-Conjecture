import PCO1PhysicalCoordinates
import Q23DerivativeDot
import Q24JointGrades

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.PhysicalCoordinates

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.Q24Realization Grad.CompatibleCompletion Grad.CompletedReality

/-- The exact physical coordinate permutation on the original completed
field grade, using the already constructed fixed value-map extension. -/
def toPhysicalGrade (parameters : PhaseParameters) (grade : ℕ) :
    AGrade parameters 3 grade →L[ℂ] AGrade parameters 3 grade :=
  q23ValueMapCompleted parameters toPhysicalValue

theorem toPhysicalGrade_core (parameters : PhaseParameters) (grade : ℕ)
    (field : ACore parameters 3) :
    toPhysicalGrade parameters grade (fieldEmbed parameters 3 grade field) =
      fieldEmbed parameters 3 grade (toPhysicalCore parameters field) :=
  q23ValueMapCompleted_core parameters toPhysicalValue field

theorem toPhysicalGrade_norm (parameters : PhaseParameters) (grade : ℕ)
    (field : AGrade parameters 3 grade) :
    ‖toPhysicalGrade parameters grade field‖ = ‖field‖ := by
  refine isClosed_property (fieldEmbed_denseRange parameters 3 grade)
    (isClosed_eq (toPhysicalGrade parameters grade).continuous.norm continuous_norm) ?_ field
  intro core
  rw [toPhysicalGrade_core, fieldEmbed_norm, fieldEmbed_norm, toPhysicalCore_norm]

theorem toPhysicalGrade_norm_le (parameters : PhaseParameters) (grade : ℕ) :
    ‖toPhysicalGrade parameters grade‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro field
  rw [toPhysicalGrade_norm, one_mul]

theorem toPhysicalGrade_involutive (parameters : PhaseParameters) (grade : ℕ)
    (field : AGrade parameters 3 grade) :
    toPhysicalGrade parameters grade (toPhysicalGrade parameters grade field) = field := by
  refine isClosed_property (fieldEmbed_denseRange parameters 3 grade)
    (isClosed_eq ((toPhysicalGrade parameters grade).continuous.comp
      (toPhysicalGrade parameters grade).continuous) continuous_id) ?_ field
  intro core
  dsimp only [Function.comp_apply]
  rw [toPhysicalGrade_core, toPhysicalGrade_core, toPhysicalCore_involutive]
  rfl

theorem toPhysicalGrade_lowering {lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (field : AGrade parameters 3 upper) :
    completedInclusion parameters ordered (toPhysicalGrade parameters upper field) =
      toPhysicalGrade parameters lower (completedInclusion parameters ordered field) := by
  refine isClosed_property (fieldEmbed_denseRange parameters 3 upper)
    (isClosed_eq ((completedInclusion parameters ordered).continuous.comp
      (toPhysicalGrade parameters upper).continuous)
      ((toPhysicalGrade parameters lower).continuous.comp
        (completedInclusion parameters ordered).continuous)) ?_ field
  intro core
  dsimp only [Function.comp_apply]
  rw [toPhysicalGrade_core]
  change completedInclusion parameters ordered (aGradeEta parameters
    (GradeCore.ofCoreLinear (toPhysicalCore parameters core))) =
      toPhysicalGrade parameters lower (completedInclusion parameters ordered
        (aGradeEta parameters (GradeCore.ofCoreLinear core)))
  rw [completedInclusion_apply_eta, completedInclusion_apply_eta]
  exact (toPhysicalGrade_core parameters lower core).symm

theorem toPhysicalGrade_conjugate (parameters : PhaseParameters) (grade : ℕ)
    (field : AGrade parameters 3 grade) :
    aGradeConjugationCLM parameters 3 grade (toPhysicalGrade parameters grade field) =
      toPhysicalGrade parameters grade (aGradeConjugationCLM parameters 3 grade field) := by
  refine isClosed_property (fieldEmbed_denseRange parameters 3 grade)
    (isClosed_eq ((aGradeConjugationCLM parameters 3 grade).continuous.comp
      (toPhysicalGrade parameters grade).continuous)
      ((toPhysicalGrade parameters grade).continuous.comp
        (aGradeConjugationCLM parameters 3 grade).continuous)) ?_ field
  intro core
  dsimp only [Function.comp_apply]
  rw [toPhysicalGrade_core]
  change aGradeConjugationCLM parameters 3 grade
      (aGradeEta parameters (GradeCore.ofCoreLinear (toPhysicalCore parameters core))) =
    toPhysicalGrade parameters grade
      (aGradeConjugationCLM parameters 3 grade (aGradeEta parameters (GradeCore.ofCoreLinear core)))
  rw [aGradeConjugation_eta, aGradeConjugation_eta]
  change fieldEmbed parameters 3 grade (cartesianCoreConjugation parameters (toPhysicalCore parameters core)) =
    toPhysicalGrade parameters grade (fieldEmbed parameters 3 grade (cartesianCoreConjugation parameters core))
  rw [toPhysicalCore_conjugate, toPhysicalGrade_core]

end Grad.PhysicalCoordinates
