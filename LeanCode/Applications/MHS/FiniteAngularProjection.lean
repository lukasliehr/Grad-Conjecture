import TangentialCore
import TangentialZeroJets

noncomputable section

open scoped BigOperators

namespace Grad.Constraints

open Grad.ClosedJets Grad.CartesianState

def selectedAngularJetLinear (dimension : ℕ) (modes : Finset ℤ) :
    ClosedJet dimension →ₗ[ℂ] ClosedJet dimension :=
  ∑ mode ∈ modes, angularClosedJetLinear dimension mode

def selectedAngularJet {dimension : ℕ} (modes : Finset ℤ) (field : ClosedJet dimension) :
    ClosedJet dimension := selectedAngularJetLinear dimension modes field

theorem selectedAngularJet_eq {dimension : ℕ} (modes : Finset ℤ) (field : ClosedJet dimension) :
    selectedAngularJet modes field = ∑ mode ∈ modes, angularClosedJet mode field := by
  simp only [selectedAngularJet, selectedAngularJetLinear, LinearMap.sum_apply]
  rfl

theorem angularClosedJet_selected {dimension : ℕ} (modes : Finset ℤ) (mode : ℤ)
    (field : ClosedJet dimension) :
    angularClosedJet mode (selectedAngularJet modes field) =
      if mode ∈ modes then angularClosedJet mode field else 0 := by
  rw [selectedAngularJet_eq]
  change angularClosedJetLinear dimension mode (∑ selected ∈ modes, angularClosedJet selected field) = _
  rw [map_sum]
  change (∑ selected ∈ modes, angularClosedJet mode (angularClosedJet selected field)) = _
  simp_rw [angularClosedJet_projection]
  simp

theorem selectedAngularJet_idempotent {dimension : ℕ} (modes : Finset ℤ)
    (field : ClosedJet dimension) :
    selectedAngularJet modes (selectedAngularJet modes field) = selectedAngularJet modes field := by
  calc
    _ = ∑ mode ∈ modes, angularClosedJet mode (selectedAngularJet modes field) :=
      selectedAngularJet_eq modes _
    _ = ∑ mode ∈ modes, angularClosedJet mode field := by
      apply Finset.sum_congr rfl
      intro mode member
      rw [angularClosedJet_selected, if_pos member]
    _ = _ := (selectedAngularJet_eq modes field).symm

def excludedAngularJetLinear (dimension : ℕ) (modes : Finset ℤ) :
    ClosedJet dimension →ₗ[ℂ] ClosedJet dimension :=
  LinearMap.id - selectedAngularJetLinear dimension modes

def excludedAngularJet {dimension : ℕ} (modes : Finset ℤ) (field : ClosedJet dimension) :
    ClosedJet dimension := excludedAngularJetLinear dimension modes field

theorem excludedAngularJet_idempotent {dimension : ℕ} (modes : Finset ℤ)
    (field : ClosedJet dimension) :
    excludedAngularJet modes (excludedAngularJet modes field) = excludedAngularJet modes field := by
  change (field - selectedAngularJet modes field) -
    selectedAngularJetLinear dimension modes (field - selectedAngularJet modes field) =
      field - selectedAngularJet modes field
  rw [map_sub]
  change (field - selectedAngularJet modes field) -
    (selectedAngularJet modes field - selectedAngularJet modes (selectedAngularJet modes field)) = _
  rw [selectedAngularJet_idempotent, sub_self, sub_zero]

def excludedAngularGradeCore {dimension grade : ℕ} (parameters : PhaseParameters)
    (modes : Finset ℤ) : GradeCore parameters dimension grade →L[ℂ] GradeCore parameters dimension grade :=
  ContinuousLinearMap.id ℂ _ - ∑ mode ∈ modes, angularGradeCoreContinuous parameters mode

theorem excludedAngularGradeCore_cell {dimension grade : ℕ} (parameters : PhaseParameters)
    (modes : Finset ℤ) (field : GradeCore parameters dimension grade) (cell : ℤ) :
    (excludedAngularGradeCore parameters modes field).toCore.1 cell =
      excludedAngularJet modes (field.toCore.1 cell) := by
  simp only [excludedAngularGradeCore, sub_apply, ContinuousLinearMap.id_apply,
    sum_apply, excludedAngularJet, excludedAngularJetLinear,
    LinearMap.sub_apply, LinearMap.id_apply, selectedAngularJetLinear, LinearMap.sum_apply]
  change field.toCore.1 cell - ((∑ mode ∈ modes, angularGradeCoreContinuous parameters mode field).toCore.1 cell) = _
  congr 1
  let evaluation : GradeCore parameters dimension grade →ₗ[ℂ] ClosedJet dimension :=
    { toFun := fun source => source.toCore.1 cell
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change evaluation (∑ mode ∈ modes, angularGradeCoreContinuous parameters mode field) = _
  rw [map_sum]
  rfl

theorem excludedAngularGradeCore_norm_le {dimension grade : ℕ} (parameters : PhaseParameters)
    (modes : Finset ℤ) (field : GradeCore parameters dimension grade) :
    ‖excludedAngularGradeCore parameters modes field‖ ≤
      (1 + modes.card * orthogonalGradeConstant grade) * ‖field‖ := by
  rw [excludedAngularGradeCore, sub_apply, ContinuousLinearMap.id_apply, sum_apply]
  calc
    _ ≤ ‖field‖ + ∑ mode ∈ modes, ‖angularGradeCoreContinuous parameters mode field‖ :=
      (norm_sub_le _ _).trans (add_le_add (le_refl _) (norm_sum_le _ _))
    _ ≤ ‖field‖ + ∑ _mode ∈ modes, orthogonalGradeConstant grade * ‖field‖ :=
      add_le_add (le_refl _) (Finset.sum_le_sum (fun mode _ => angularGradeCore_norm_le parameters mode field))
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- The paper's P_{>=3}: remove exactly the five modes -2,-1,0,1,2. -/
def lowAngularModes : Finset ℤ := {-2, -1, 0, 1, 2}

theorem lowAngularModes_card : lowAngularModes.card = 5 := by decide

theorem excludedAngularJet_preserves_zero_derivatives {dimension order : ℕ}
    (modes : Finset ℤ) (field : ClosedJet dimension)
    (zeroJets : ∀ word : CartesianWord order, closedDerivative field order word
      ⟨0, by simp [closedUnitDisk]⟩ = 0) (word : CartesianWord order) :
    closedDerivative (excludedAngularJet modes field) order word
      ⟨0, by simp [closedUnitDisk]⟩ = 0 := by
  change closedDerivative (field - selectedAngularJet modes field) order word _ = 0
  rw [selectedAngularJet_eq]
  change (closedDerivativeLinear order word (field - ∑ mode ∈ modes, angularClosedJet mode field)) _ = 0
  rw [map_sub, map_sum, ContinuousMap.sub_apply, ContinuousMap.sum_apply]
  change closedDerivative field order word _ -
    ∑ mode ∈ modes, closedDerivative (angularClosedJet mode field) order word _ = 0
  simp only [zeroJets word, angularClosedJet_preserves_zero_derivatives _ field zeroJets word,
    Finset.sum_const_zero, sub_self]

end Grad.Constraints
