import COR13Consumer
import FC6Monotone

noncomputable section

namespace Grad.CompatibleCompletion

open Grad.ClosedJets Grad.CartesianState Grad.FourierGrade Grad.COR12Extension Grad.COR13Completion

/-- The literal grade-lowering map into the lower original completion. -/
def inclusionCore {dimension lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) :
    GradeCore parameters dimension upper →ₗ[ℂ] AGrade parameters dimension lower :=
  (aGradeEta parameters).toLinearMap.comp (gradeCoreInclusionLinear parameters ordered)

theorem inclusionCore_norm_le {dimension lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (field : GradeCore parameters dimension upper) :
    ‖inclusionCore parameters ordered field‖ ≤ 1 * ‖field‖ := by
  change ‖aGradeEta parameters (gradeCoreInclusionLinear parameters ordered field)‖ ≤ _
  rw [aGradeEta_norm, one_mul]
  exact cartesianGrade_norm_mono parameters ordered field.toCore

/-- The canonical constant-one inclusion of the actual original completions. -/
def completedInclusion {dimension lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) :
    AGrade parameters dimension upper →L[ℂ] AGrade parameters dimension lower :=
  denseCoreExtension parameters (inclusionCore parameters ordered) 1
    (inclusionCore_norm_le parameters ordered)

theorem completedInclusion_apply_eta {dimension lower upper : ℕ}
    (parameters : PhaseParameters) (ordered : lower ≤ upper)
    (field : GradeCore parameters dimension upper) :
    completedInclusion parameters ordered (aGradeEta parameters field) =
      aGradeEta parameters (GradeCore.ofCoreLinear field.toCore) :=
  denseCoreExtension_apply_eta parameters _ _ _ field

theorem completedInclusion_norm_le_one {dimension lower upper : ℕ}
    (parameters : PhaseParameters) (ordered : lower ≤ upper) :
    ‖completedInclusion (dimension := dimension) parameters ordered‖ ≤ 1 :=
  denseCoreExtension_norm_le parameters _ _ zero_le_one _

theorem completedInclusion_self {dimension grade : ℕ} (parameters : PhaseParameters) :
    completedInclusion parameters (le_refl grade) =
      ContinuousLinearMap.id ℂ (AGrade parameters dimension grade) := by
  apply denseCoreContinuousLinearMap_ext parameters
  intro field
  rw [completedInclusion_apply_eta]
  rfl

theorem completedInclusion_comp {dimension high middle low : ℕ}
    (parameters : PhaseParameters) (middleHigh : middle ≤ high) (lowMiddle : low ≤ middle) :
    (completedInclusion (dimension := dimension) parameters lowMiddle).comp
      (completedInclusion parameters middleHigh) =
        completedInclusion parameters (lowMiddle.trans middleHigh) := by
  apply denseCoreContinuousLinearMap_ext parameters
  intro field
  rw [ContinuousLinearMap.comp_apply, completedInclusion_apply_eta,
    completedInclusion_apply_eta, completedInclusion_apply_eta]
  rfl

theorem extension_inclusion_naturality {dimension lower upper : ℕ}
    (parameters : PhaseParameters) (ordered : lower ≤ upper) :
    (completedExtension (dimension := dimension) (grade := lower) parameters).comp
      (completedInclusion parameters ordered) =
        (inclusion upper lower ordered).comp (completedExtension parameters) := by
  apply denseCoreContinuousLinearMap_ext parameters
  intro field
  simp only [ContinuousLinearMap.comp_apply, completedInclusion_apply_eta,
    completedExtension_apply_eta, GradeCore.toCore_ofCore, inclusion_coreToGrade]

theorem retraction_inclusion_naturality {dimension lower upper : ℕ}
    (parameters : PhaseParameters) (ordered : lower ≤ upper) :
    (completedInclusion (dimension := dimension) parameters ordered).comp
      (completedRetraction parameters) =
        (completedRetraction parameters).comp (inclusion upper lower ordered) := by
  apply DFunLike.ext
  have equalFunctions := (fourierCore_denseRange dimension upper).equalizer
    ((completedInclusion parameters ordered).comp (completedRetraction parameters)).continuous
    ((completedRetraction parameters).comp (inclusion upper lower ordered)).continuous (by
      funext values
      simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
        completedRetraction_apply_core, completedInclusion_apply_eta, GradeCore.toCore_ofCore,
        inclusion_coreToGrade])
  exact congrFun equalFunctions

/-- Completed injectivity uses the faithful Fourier realization and exact
naturality, not merely monotonicity of the original norms. -/
theorem completedInclusion_injective {dimension lower upper : ℕ}
    (parameters : PhaseParameters) (ordered : lower ≤ upper) :
    Function.Injective (completedInclusion (dimension := dimension) parameters ordered) := by
  intro first second equality
  apply completedExtension_injective (grade := upper) parameters
  apply inclusion_injective upper lower ordered
  have natural := DFunLike.congr_fun (extension_inclusion_naturality
    (dimension := dimension) parameters ordered)
  simp only [ContinuousLinearMap.comp_apply] at natural
  rw [← natural first, ← natural second]
  change completedExtension parameters (completedInclusion parameters ordered first) =
    completedExtension parameters (completedInclusion parameters ordered second)
  rw [equality]

end Grad.CompatibleCompletion
