import AveragesProof
import FC10Extension

noncomputable section

namespace Grad.Constraints

open Grad.ClosedJets Grad.CartesianState

/-- Canonical extension of an actual original-grade operator. The target
uses the literal AGrade norm completion, not a transported substitute. -/
def completeOriginalMap {dimension grade : ℕ} (parameters : PhaseParameters)
    (mapping : GradeCore parameters dimension grade →L[ℂ] GradeCore parameters dimension grade) :
    AGrade parameters dimension grade →L[ℂ] AGrade parameters dimension grade :=
  ((aGradeEta parameters).toContinuousLinearMap.comp mapping).fromCompletion

theorem completeOriginalMap_eta {dimension grade : ℕ} (parameters : PhaseParameters)
    (mapping : GradeCore parameters dimension grade →L[ℂ] GradeCore parameters dimension grade)
    (field : GradeCore parameters dimension grade) :
    completeOriginalMap parameters mapping (aGradeEta parameters field) =
      aGradeEta parameters (mapping field) := by
  exact ContinuousLinearMap.fromCompletion_apply_coe _ field

theorem completeOriginalMap_bound {dimension grade : ℕ} (parameters : PhaseParameters)
    (mapping : GradeCore parameters dimension grade →L[ℂ] GradeCore parameters dimension grade)
    (constant : ℝ) (bound : ∀ field, ‖mapping field‖ ≤ constant * ‖field‖)
    (field : AGrade parameters dimension grade) :
    ‖completeOriginalMap parameters mapping field‖ ≤ constant * ‖field‖ := by
  refine UniformSpace.Completion.induction_on field (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro source
  change ‖completeOriginalMap parameters mapping (aGradeEta parameters source)‖ ≤
    constant * ‖aGradeEta parameters source‖
  rw [completeOriginalMap_eta, aGradeEta_norm, aGradeEta_norm]
  exact bound source

def angularCompleted {dimension grade : ℕ} (parameters : PhaseParameters) (mode : ℤ) :
    AGrade parameters dimension grade →L[ℂ] AGrade parameters dimension grade :=
  completeOriginalMap parameters (angularGradeCoreContinuous parameters mode)

theorem angularCompleted_eta {dimension grade : ℕ} (parameters : PhaseParameters) (mode : ℤ)
    (field : GradeCore parameters dimension grade) :
    angularCompleted parameters mode (aGradeEta parameters field) =
      aGradeEta parameters (angularGradeCore parameters mode field) := completeOriginalMap_eta parameters _ field

theorem angularCompleted_bound {dimension grade : ℕ} (parameters : PhaseParameters) (mode : ℤ)
    (field : AGrade parameters dimension grade) :
    ‖angularCompleted parameters mode field‖ ≤ orthogonalGradeConstant grade * ‖field‖ :=
  completeOriginalMap_bound parameters
    (angularGradeCoreContinuous (dimension := dimension) (grade := grade) parameters mode)
    (orthogonalGradeConstant grade) (fun source => angularGradeCore_norm_le parameters mode source) field

theorem angularGradeCore_projection {dimension grade : ℕ} (parameters : PhaseParameters)
    (first second : ℤ) (field : GradeCore parameters dimension grade) :
    angularGradeCore parameters first (angularGradeCore parameters second field) =
      if first = second then angularGradeCore parameters first field else 0 := by
  apply GradeCore.ext
  apply Subtype.ext
  funext cell
  by_cases equalModes : first = second
  · simp only [equalModes, ite_true]
    exact (angularClosedJet_projection second second (field.toCore.1 cell)).trans (if_pos rfl)
  · simp only [equalModes, ite_false]
    exact (angularClosedJet_projection first second (field.toCore.1 cell)).trans (if_neg equalModes)

theorem angularCompleted_projection {dimension grade : ℕ} (parameters : PhaseParameters)
    (first second : ℤ) :
    (angularCompleted (dimension := dimension) (grade := grade) parameters first).comp
        (angularCompleted parameters second) =
      if first = second then angularCompleted parameters first else 0 := by
  apply denseCoreContinuousLinearMap_ext parameters
  intro field
  rw [ContinuousLinearMap.comp_apply, angularCompleted_eta, angularCompleted_eta,
    angularGradeCore_projection]
  by_cases equalModes : first = second
  · simp only [equalModes, ite_true, angularCompleted_eta]
  · simp only [equalModes, ite_false, map_zero, zero_apply]

def tangentialCompleted {grade : ℕ} (parameters : PhaseParameters) :
    AGrade parameters 2 grade →L[ℂ] AGrade parameters 2 grade :=
  completeOriginalMap parameters (tangentialGradeCore parameters)

theorem tangentialCompleted_eta {grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters 2 grade) :
    tangentialCompleted parameters (aGradeEta parameters field) =
      aGradeEta parameters (tangentialGradeCore parameters field) := completeOriginalMap_eta parameters _ field

theorem tangentialCompleted_bound {grade : ℕ} (parameters : PhaseParameters)
    (field : AGrade parameters 2 grade) :
    ‖tangentialCompleted parameters field‖ ≤ tangentialGradeConstant grade * ‖field‖ :=
  completeOriginalMap_bound parameters _ _ (tangentialGradeCore_norm_le parameters) field

theorem tangentialCompleted_projection {grade : ℕ} (parameters : PhaseParameters) :
    (tangentialCompleted (grade := grade) parameters).comp (tangentialCompleted parameters) =
      tangentialCompleted parameters := by
  apply denseCoreContinuousLinearMap_ext parameters
  intro field
  rw [ContinuousLinearMap.comp_apply, tangentialCompleted_eta, tangentialCompleted_eta,
    tangentialGradeCore_idempotent]

def highModesCompleted {dimension grade : ℕ} (parameters : PhaseParameters) :
    AGrade parameters dimension grade →L[ℂ] AGrade parameters dimension grade :=
  completeOriginalMap parameters (excludedAngularGradeCore parameters lowAngularModes)

theorem highModesCompleted_eta {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters dimension grade) :
    highModesCompleted parameters (aGradeEta parameters field) =
      aGradeEta parameters (excludedAngularGradeCore parameters lowAngularModes field) :=
  completeOriginalMap_eta parameters _ field

theorem highModesCompleted_bound {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : AGrade parameters dimension grade) :
    ‖highModesCompleted parameters field‖ ≤ (1 + 5 * orthogonalGradeConstant grade) * ‖field‖ :=
  completeOriginalMap_bound parameters _ _ (averages.high_modes_bound parameters) field

theorem excludedAngularGradeCore_projection {dimension grade : ℕ} (parameters : PhaseParameters)
    (modes : Finset ℤ) (field : GradeCore parameters dimension grade) :
    excludedAngularGradeCore parameters modes (excludedAngularGradeCore parameters modes field) =
      excludedAngularGradeCore parameters modes field := by
  apply GradeCore.ext
  apply Subtype.ext
  funext cell
  simp only [excludedAngularGradeCore_cell, excludedAngularJet_idempotent]

theorem highModesCompleted_projection {dimension grade : ℕ} (parameters : PhaseParameters) :
    (highModesCompleted (dimension := dimension) (grade := grade) parameters).comp (highModesCompleted parameters) =
      highModesCompleted parameters := by
  apply denseCoreContinuousLinearMap_ext parameters
  intro field
  rw [ContinuousLinearMap.comp_apply, highModesCompleted_eta, highModesCompleted_eta,
    excludedAngularGradeCore_projection]

end Grad.Constraints
