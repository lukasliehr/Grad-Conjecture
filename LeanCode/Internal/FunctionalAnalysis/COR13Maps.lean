import COR12Consumer
import FC10Extension
import Mathlib.Analysis.Normed.Operator.Extend

noncomputable section

namespace Grad.COR13Completion

open Grad.ClosedJets Grad.CartesianState Grad.FourierGrade Grad.COR12Extension

/-- Extend the actual weighted Fourier map from the original grade core to
its literal norm completion. No transported Fourier norm is installed. -/
def completedExtension {dimension grade : ℕ} (parameters : PhaseParameters) :
    AGrade parameters dimension grade →L[ℂ] JGrade (ComplexEuclidean dimension) grade :=
  denseCoreExtension parameters (Consumer.gradeCoreFourierLinear parameters)
    (sameGradeConstant grade)
    (fun field => weightedFourierExtension_norm_le parameters field.toCore grade)

theorem completedExtension_apply_eta {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : GradeCore parameters dimension grade) :
    completedExtension parameters (aGradeEta parameters field) =
      coreToGrade grade (weightedFourierExtension parameters field.toCore) := by
  exact denseCoreExtension_apply_eta parameters _ _ _ field

theorem completedExtension_norm_le {dimension grade : ℕ} (parameters : PhaseParameters) :
    ‖completedExtension (dimension := dimension) (grade := grade) parameters‖ ≤
      sameGradeConstant grade :=
  denseCoreExtension_norm_le parameters _ _ (sameGradeConstant_nonnegative grade) _

/-- The reverse core map lands in the original completion using its isometric
core embedding; the input is the accepted all-grade coefficient core. -/
def retractionCore {dimension grade : ℕ} (parameters : PhaseParameters) :
    JCore (ComplexEuclidean dimension) →ₗ[ℂ] AGrade parameters dimension grade :=
  (aGradeEta parameters).toLinearMap.comp
    (GradeCore.ofCoreLinear.comp (weightedFourierRetraction parameters))

theorem retractionCore_apply {dimension grade : ℕ} (parameters : PhaseParameters)
    (values : JCore (ComplexEuclidean dimension)) :
    retractionCore (grade := grade) parameters values =
      aGradeEta parameters (GradeCore.ofCoreLinear
        (weightedFourierRetraction parameters values)) := rfl

theorem retractionCore_norm_le {dimension grade : ℕ} (parameters : PhaseParameters)
    (values : JCore (ComplexEuclidean dimension)) :
    ‖retractionCore (grade := grade) parameters values‖ ≤
      sameGradeConstant grade * ‖coreToGrade grade values‖ := by
  rw [retractionCore_apply, aGradeEta_norm]
  exact weightedFourierRetraction_norm_le parameters values grade

theorem fourierCore_denseRange (dimension grade : ℕ) :
    DenseRange (coreToGrade (Value := ComplexEuclidean dimension) grade) :=
  coreToGrade_dense grade

/-- Extend the actual COR12 restriction from its dense all-grade Fourier
core, using the proved relative bound in the original completion norm. -/
def completedRetraction {dimension grade : ℕ} (parameters : PhaseParameters) :
    JGrade (ComplexEuclidean dimension) grade →L[ℂ] AGrade parameters dimension grade :=
  (retractionCore parameters).extendOfNorm (coreToGrade grade)

theorem completedRetraction_apply_core {dimension grade : ℕ}
    (parameters : PhaseParameters) (values : JCore (ComplexEuclidean dimension)) :
    completedRetraction parameters (coreToGrade grade values) =
      aGradeEta parameters (GradeCore.ofCoreLinear
        (weightedFourierRetraction parameters values)) := by
  exact LinearMap.extendOfNorm_eq (fourierCore_denseRange dimension grade)
    ⟨sameGradeConstant grade, retractionCore_norm_le parameters⟩ values

theorem completedRetraction_norm_le {dimension grade : ℕ} (parameters : PhaseParameters) :
    ‖completedRetraction (dimension := dimension) (grade := grade) parameters‖ ≤
      sameGradeConstant grade :=
  LinearMap.opNorm_extendOfNorm_le (fourierCore_denseRange dimension grade)
    (sameGradeConstant_nonnegative grade) (retractionCore_norm_le parameters)

theorem completedRetraction_extension {dimension grade : ℕ} (parameters : PhaseParameters) :
    (completedRetraction parameters).comp (completedExtension parameters) =
      ContinuousLinearMap.id ℂ (AGrade parameters dimension grade) := by
  apply denseCoreContinuousLinearMap_ext parameters
  intro field
  rw [ContinuousLinearMap.comp_apply, completedExtension_apply_eta,
    completedRetraction_apply_core, weightedFourierRetraction_extension]
  rfl

theorem completedRetraction_extension_apply {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : AGrade parameters dimension grade) :
    completedRetraction parameters (completedExtension parameters field) = field :=
  DFunLike.congr_fun (completedRetraction_extension parameters) field

theorem completedExtension_injective {dimension grade : ℕ} (parameters : PhaseParameters) :
    Function.Injective (completedExtension (dimension := dimension) (grade := grade) parameters) :=
  Function.LeftInverse.injective (completedRetraction_extension_apply parameters)

end Grad.COR13Completion
