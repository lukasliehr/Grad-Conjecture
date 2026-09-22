import GQC27AxialCore

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Frame

theorem apAxial_exists (L sigma gamma ell : ℝ) (dimension grade : ℕ) :
    ∃ mapping : apGrade L sigma gamma ell dimension (grade + 1) →L[ℂ] apGrade L sigma gamma ell dimension grade,
      (∀ core, mapping (apFiniteInto L sigma gamma ell core) = apFiniteInto L sigma gamma ell (axialCore L ell dimension core)) ∧
      (∀ field, ‖mapping field‖ ≤ apLoweringConstant grade * ‖field‖) :=
  apDense_extension (apFiniteInto (grade := grade + 1) L sigma gamma ell)
    (apFiniteInto_injective L sigma gamma ell) (apFiniteInto_denseRange L sigma gamma ell)
    ((apFiniteInto (grade := grade) L sigma gamma ell).comp (axialCore L ell dimension))
    (apLoweringConstant grade) (apLoweringConstant_nonnegative grade) (axialFinite_bound L sigma gamma ell)

def apAxial (L sigma gamma ell : ℝ) (dimension grade : ℕ) :
    apGrade L sigma gamma ell dimension (grade + 1) →L[ℂ] apGrade L sigma gamma ell dimension grade :=
  (apAxial_exists L sigma gamma ell dimension grade).choose

theorem apAxial_core (L sigma gamma ell : ℝ) (dimension grade : ℕ) (core : ℤ →₀ ClosedJet dimension) :
    apAxial L sigma gamma ell dimension grade (apFiniteInto L sigma gamma ell core) =
      apFiniteInto L sigma gamma ell (axialCore L ell dimension core) :=
  (apAxial_exists L sigma gamma ell dimension grade).choose_spec.1 core

theorem apAxial_bound (L sigma gamma ell : ℝ) (dimension grade : ℕ)
    (field : apGrade L sigma gamma ell dimension (grade + 1)) :
    ‖apAxial L sigma gamma ell dimension grade field‖ ≤ apLoweringConstant grade * ‖field‖ :=
  (apAxial_exists L sigma gamma ell dimension grade).choose_spec.2 field

theorem apAxial_lowering {dimension low high : ℕ} (L sigma gamma ell : ℝ) (ordered : low ≤ high)
    (field : apGrade L sigma gamma ell dimension (high + 1)) :
    apLowering L sigma gamma ell ordered (apAxial L sigma gamma ell dimension high field) =
      apAxial L sigma gamma ell dimension low (apLowering L sigma gamma ell (Nat.add_le_add_right ordered 1) field) := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := high + 1) L sigma gamma ell)
    (isClosed_eq ((apLowering L sigma gamma ell ordered).continuous.comp
      (apAxial L sigma gamma ell dimension high).continuous)
      ((apAxial L sigma gamma ell dimension low).continuous.comp
        (apLowering L sigma gamma ell (Nat.add_le_add_right ordered 1)).continuous)) _ field
  intro core
  simp only [Function.comp_apply]
  rw [apAxial_core, apLowering_core, apLowering_core, apAxial_core]

def apSmoothAxial (L sigma gamma ell : ℝ) (dimension : ℕ) :
    APSmooth L sigma gamma ell dimension →ₗ[ℂ] APSmooth L sigma gamma ell dimension where
  toFun field := ⟨fun grade => apAxial L sigma gamma ell dimension grade (field.val (grade + 1)),
    fun low high ordered => by
      rw [apAxial_lowering, field.property (low + 1) (high + 1) (Nat.add_le_add_right ordered 1)]⟩
  map_add' first second := by
    apply Subtype.ext
    funext grade
    exact (apAxial L sigma gamma ell dimension grade).map_add (first.val (grade + 1)) (second.val (grade + 1))
  map_smul' scalar field := by
    apply Subtype.ext
    funext grade
    exact (apAxial L sigma gamma ell dimension grade).map_smul scalar (field.val (grade + 1))

theorem apAxial_trace {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension grade : ℕ} (large : 2 ≤ grade) (field : apGrade L sigma gamma ell dimension (grade + 1))
    (cell : ℤ) :
    apTrace admissible large cell (apAxial L sigma gamma ell dimension grade field) =
      seedScaledFrequency L ell cell • apTrace admissible (large.trans (Nat.le_succ grade)) cell field := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := grade + 1) L sigma gamma ell)
    (isClosed_eq ((apTrace admissible large cell).continuous.comp (apAxial L sigma gamma ell dimension grade).continuous)
      ((apTrace admissible (large.trans (Nat.le_succ grade)) cell).continuous.const_smul (seedScaledFrequency L ell cell))) _ field
  intro core
  simp only [Function.comp_apply, Pi.smul_apply]
  rw [apAxial_core, apTrace_core, apTrace_core, axialCore_apply, closedJet_value_smul]

theorem apSmoothAxial_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (field : APSmooth L sigma gamma ell dimension) (cell : ℤ) :
    apSmoothJet admissible dimension cell (apSmoothAxial L sigma gamma ell dimension field) =
      seedScaledFrequency L ell cell • apSmoothJet admissible dimension cell field := by
  apply closedJet_eq_of_value_eq
  rw [closedJet_value_smul]
  change (apFamilyJet (apSmoothAxial L sigma gamma ell dimension field).val _ cell).value =
    seedScaledFrequency L ell cell • (apFamilyJet field.val field.property cell).value
  rw [apFamilyJet_value_trace admissible (apSmoothAxial L sigma gamma ell dimension field).val
    (apSmoothAxial L sigma gamma ell dimension field).property (by omega : 2 ≤ 2) cell,
    apFamilyJet_value_trace admissible field.val field.property (by omega : 2 ≤ 3) cell]
  exact apAxial_trace admissible (by omega : 2 ≤ 2) (field.val 3) cell

end Grad.GaugeCoefficients.Physical.Compensated
