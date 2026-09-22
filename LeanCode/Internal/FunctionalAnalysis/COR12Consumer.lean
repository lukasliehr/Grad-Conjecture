import COR12Proof

noncomputable section

namespace Grad.COR12Extension.Consumer

open Grad.ClosedJets
open Grad.CartesianState
open Grad.FourierGrade

/-- The literal COR13 input map from the original normed grade core into
the complete Fourier grade. Its norm is the original Cartesian norm. -/
def gradeCoreFourierLinear {dimension grade : ℕ} (parameters : PhaseParameters) :
    GradeCore parameters dimension grade →ₗ[ℂ] JGrade (ComplexEuclidean dimension) grade :=
  (coreToGrade grade).comp ((weightedFourierExtension parameters).comp GradeCore.toCoreLinear)

def gradeCoreFourierContinuous {dimension grade : ℕ} (parameters : PhaseParameters) :
    GradeCore parameters dimension grade →L[ℂ] JGrade (ComplexEuclidean dimension) grade :=
  (gradeCoreFourierLinear parameters).mkContinuous (sameGradeConstant grade)
    (fun field => weightedFourierExtension_norm_le parameters field.toCore grade)

theorem gradeCoreFourierContinuous_apply {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : GradeCore parameters dimension grade) :
    gradeCoreFourierContinuous parameters field =
      coreToGrade grade (weightedFourierExtension parameters field.toCore) := rfl

theorem gradeCoreFourierContinuous_norm_le {dimension grade : ℕ}
    (parameters : PhaseParameters) :
    ‖gradeCoreFourierContinuous (dimension := dimension) (grade := grade) parameters‖ ≤
      sameGradeConstant grade := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sameGradeConstant_nonnegative grade)
  intro field
  exact weightedFourierExtension_norm_le parameters field.toCore grade

theorem gradeCoreFourierContinuous_injective {dimension grade : ℕ}
    (parameters : PhaseParameters) :
    Function.Injective
      (gradeCoreFourierContinuous (dimension := dimension) (grade := grade) parameters) := by
  intro first second equality
  apply GradeCore.ext
  have coefficientEquality : weightedFourierExtension parameters first.toCore =
      weightedFourierExtension parameters second.toCore :=
    coreToGrade_injective grade equality
  have retracted := congrArg (weightedFourierRetraction parameters) coefficientEquality
  simpa only [weightedFourierRetraction_extension] using retracted

/-- The reverse comparison retains exactly the same Cartesian grade and the
same phase parameters as the extension consumer. -/
theorem exact_core_retraction_and_reverse_bound {dimension : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension) (grade : ℕ) :
    weightedFourierRetraction parameters (weightedFourierExtension parameters field) = field ∧
      ‖GradeCore.ofCoreLinear (grade := grade) field‖ ≤ sameGradeConstant grade *
        ‖coreToGrade grade (weightedFourierExtension parameters field)‖ := by
  refine ⟨weightedFourierRetraction_extension parameters field, ?_⟩
  have bound := weightedFourierRetraction_norm_le parameters
    (weightedFourierExtension parameters field) grade
  rwa [weightedFourierRetraction_extension] at bound

end Grad.COR12Extension.Consumer
