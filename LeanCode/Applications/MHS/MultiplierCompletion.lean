import MultiplierShift

noncomputable section

namespace Grad.Constraints.Multipliers

open Grad.ClosedJets Grad.CartesianState

def singleModeCoreToCompletion {sourceDimension targetDimension grade : ℕ}
    (parameters : PhaseParameters) (shift : ℤ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    GradeCore parameters sourceDimension grade →ₗ[ℂ] AGrade parameters targetDimension grade :=
  (aGradeEta parameters).toLinearMap.comp (singleModeGradeCore parameters shift mapping)

theorem singleModeCoreToCompletion_bound {sourceDimension targetDimension grade : ℕ}
    (parameters : PhaseParameters) (shift : ℤ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : GradeCore parameters sourceDimension grade) :
    ‖singleModeCoreToCompletion parameters shift mapping field‖ ≤
      shiftBound parameters grade shift * ‖mapping‖ * ‖field‖ := by
  change ‖aGradeEta parameters (singleModeGradeCore parameters shift mapping field)‖ ≤ _
  rw [aGradeEta_norm]
  exact singleModeGradeCore_norm_le parameters shift mapping field

def singleModeCompleted {sourceDimension targetDimension grade : ℕ}
    (parameters : PhaseParameters) (shift : ℤ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    AGrade parameters sourceDimension grade →L[ℂ] AGrade parameters targetDimension grade :=
  denseCoreExtension parameters (singleModeCoreToCompletion parameters shift mapping)
    (shiftBound parameters grade shift * ‖mapping‖)
    (singleModeCoreToCompletion_bound parameters shift mapping)

theorem singleModeCompleted_eta {sourceDimension targetDimension grade : ℕ}
    (parameters : PhaseParameters) (shift : ℤ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : GradeCore parameters sourceDimension grade) :
    singleModeCompleted parameters shift mapping (aGradeEta parameters field) =
      aGradeEta parameters (singleModeGradeCore parameters shift mapping field) :=
  denseCoreExtension_apply_eta parameters _ _ _ field

theorem singleModeCompleted_norm_le {sourceDimension targetDimension grade : ℕ}
    (parameters : PhaseParameters) (shift : ℤ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    ‖singleModeCompleted (grade := grade) parameters shift mapping‖ ≤
      shiftBound parameters grade shift * ‖mapping‖ :=
  denseCoreExtension_norm_le parameters _ _
    (mul_nonneg (shiftBound_nonnegative _ _ _) (norm_nonneg _)) _

theorem singleModeCompleted_row {sourceDimension targetDimension grade : ℕ}
    (parameters : PhaseParameters)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : GradeCore parameters sourceDimension grade) (output shift : ℤ) :
    completedCoordinates parameters
      (singleModeCompleted parameters shift (coefficients shift) (aGradeEta parameters field)) output =
      multiplierRow parameters coefficients field output shift := by
  rw [singleModeCompleted_eta, completedCoordinates_eta]
  rfl

end Grad.Constraints.Multipliers
