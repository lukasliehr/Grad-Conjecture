import AX16ZConsumer
import FC7Conjugation
import Mathlib.Analysis.Normed.Operator.Extend

noncomputable section

namespace Grad.CompletedReality

open Grad.ClosedJets Grad.CartesianState Grad.AxisCore

/-- The original dense coefficient embedding, with real scalars. -/
def aGradeEtaReal (parameters : PhaseParameters) (dimension grade : ℕ) :
    GradeCore parameters dimension grade →L[ℝ] AGrade parameters dimension grade :=
  (aGradeEta parameters).toContinuousLinearMap.restrictScalars ℝ

/-- Completion of the literal core conjugation with reversal of the integer cell. -/
def aGradeConjugationCLM (parameters : PhaseParameters) (dimension grade : ℕ) :
    AGrade parameters dimension grade →L[ℝ] AGrade parameters dimension grade :=
  ((aGradeEtaReal parameters dimension grade).comp
    (gradeCoreConjugation parameters).toContinuousLinearEquiv.toContinuousLinearMap).extend
      (aGradeEtaReal parameters dimension grade)

theorem aGradeConjugation_eta (parameters : PhaseParameters) (dimension grade : ℕ)
    (field : GradeCore parameters dimension grade) :
    aGradeConjugationCLM parameters dimension grade (aGradeEta parameters field) =
      aGradeEta parameters (gradeCoreConjugation parameters field) := by
  exact ContinuousLinearMap.extend_eq _ (aGradeEta_denseRange parameters)
    (aGradeEta parameters).isometry.isUniformInducing field

theorem aGradeConjugation_norm (parameters : PhaseParameters) (dimension grade : ℕ)
    (field : AGrade parameters dimension grade) :
    ‖aGradeConjugationCLM parameters dimension grade field‖ = ‖field‖ := by
  exact isClosed_property (aGradeEta_denseRange parameters)
    (isClosed_eq (aGradeConjugationCLM parameters dimension grade).continuous.norm continuous_norm)
    (fun core => by rw [aGradeConjugation_eta, aGradeEta_norm, aGradeEta_norm,
      (gradeCoreConjugation parameters).norm_map]) field

theorem aGradeConjugation_involutive (parameters : PhaseParameters) (dimension grade : ℕ) :
    Function.Involutive (aGradeConjugationCLM parameters dimension grade) := by
  intro field
  exact isClosed_property (aGradeEta_denseRange parameters)
    (isClosed_eq ((aGradeConjugationCLM parameters dimension grade).continuous.comp
      (aGradeConjugationCLM parameters dimension grade).continuous) continuous_id)
    (fun core => by dsimp only [Function.comp_apply, id_eq]; rw [aGradeConjugation_eta, aGradeConjugation_eta,
      gradeCoreConjugation_involutive]) field

/-- The completed real-linear isometric involution with the original M2 norm. -/
def aGradeConjugation (parameters : PhaseParameters) (dimension grade : ℕ) :
    AGrade parameters dimension grade ≃ₗᵢ[ℝ] AGrade parameters dimension grade :=
  { (aGradeConjugationCLM parameters dimension grade).toLinearMap with
    invFun := aGradeConjugationCLM parameters dimension grade
    left_inv := aGradeConjugation_involutive parameters dimension grade
    right_inv := aGradeConjugation_involutive parameters dimension grade
    norm_map' := aGradeConjugation_norm parameters dimension grade }

/-- The accepted completed axis symmetry, packaged as a real-linear isometry. -/
def axisConjugation (parameters : PhaseParameters) (dimension grade : ℕ) :
    AxisGrade parameters dimension grade ≃ₗᵢ[ℝ] AxisGrade parameters dimension grade :=
  { toFun := axisInvolution parameters dimension grade
    invFun := axisInvolution parameters dimension grade
    map_add' := axisInvolution_add parameters dimension grade
    map_smul' := fun scalar field => by
      apply lp.ext
      funext cell
      exact (cartesianPhysicalConjugation dimension).map_smul scalar (field (-cell))
    left_inv := axisInvolution_involutive parameters dimension grade
    right_inv := axisInvolution_involutive parameters dimension grade
    norm_map' := axisInvolution_norm parameters dimension grade }

end Grad.CompletedReality
