import AveragesProof

noncomputable section

namespace Grad.Constraints

open Grad.ClosedJets Grad.CartesianState

/-- The actual zero value and zero first Cartesian derivatives at the axis,
cell by cell, as used by the downstream Cartesian gauge constraints. -/
def ZeroCartesianFirstJets {dimension : ℕ} (field : ClosedJet dimension) : Prop :=
  ∀ order : ℕ, order ≤ 1 → ∀ word : CartesianWord order,
    closedDerivative field order word ⟨0, by simp [closedUnitDisk]⟩ = 0

theorem angularGauge_consumer {dimension grade : ℕ} (parameters : PhaseParameters)
    (mode : ℤ) (field : GradeCore parameters dimension grade)
    (zeroJets : ∀ cell : ℤ, ZeroCartesianFirstJets (field.toCore.1 cell)) :
    ‖angularGradeCore parameters mode field‖ ≤ orthogonalGradeConstant grade * ‖field‖ ∧
      ∀ cell : ℤ, ZeroCartesianFirstJets ((angularGradeCore parameters mode field).toCore.1 cell) := by
  refine ⟨averages.original_angular_bound parameters mode field, ?_⟩
  intro cell order low word
  exact averages.angular_zero_jets mode (field.toCore.1 cell) (zeroJets cell order low) word

theorem tangentialGauge_consumer {grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters 2 grade)
    (zeroJets : ∀ cell : ℤ, ZeroCartesianFirstJets (field.toCore.1 cell)) :
    ‖tangentialGradeCore parameters field‖ ≤ tangentialGradeConstant grade * ‖field‖ ∧
      tangentialGradeCore parameters (tangentialGradeCore parameters field) = tangentialGradeCore parameters field ∧
      ∀ cell : ℤ, ZeroCartesianFirstJets ((tangentialGradeCore parameters field).toCore.1 cell) := by
  refine ⟨averages.original_tangential_bound parameters field,
    tangentialGradeCore_idempotent parameters field, ?_⟩
  intro cell order low word
  change closedDerivative (tangentialJet (field.toCore.1 cell)) order word _ = 0
  exact averages.tangential_zero_jets (field.toCore.1 cell) (zeroJets cell order low) word

theorem highModesGauge_consumer {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters dimension grade)
    (zeroJets : ∀ cell : ℤ, ZeroCartesianFirstJets (field.toCore.1 cell)) :
    ‖excludedAngularGradeCore parameters lowAngularModes field‖ ≤
        (1 + 5 * orthogonalGradeConstant grade) * ‖field‖ ∧
      ∀ cell : ℤ, ZeroCartesianFirstJets
        ((excludedAngularGradeCore parameters lowAngularModes field).toCore.1 cell) := by
  refine ⟨averages.high_modes_bound parameters field, ?_⟩
  intro cell order low word
  rw [excludedAngularGradeCore_cell]
  exact excludedAngularJet_preserves_zero_derivatives lowAngularModes (field.toCore.1 cell)
    (zeroJets cell order low) word

end Grad.Constraints
