import GQC15APSmoothTrace

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope

def apSmoothFamilies (L sigma gamma ell : ℝ) (dimension : ℕ) :
    Submodule ℂ (APFamily L sigma gamma ell dimension) where
  carrier := {family | APFamilyCoherent family}
  zero_mem' := by intro low high ordered; exact map_zero _
  add_mem' first second := by
    intro low high ordered
    change apLowering L sigma gamma ell ordered (_ + _) = _ + _
    rw [map_add, first low high ordered, second low high ordered]
  smul_mem' scalar family coherent := by
    intro low high ordered
    change apLowering L sigma gamma ell ordered (scalar • family high) = scalar • family low
    rw [map_smul, coherent low high ordered]

abbrev APSmooth (L sigma gamma ell : ℝ) (dimension : ℕ) := apSmoothFamilies L sigma gamma ell dimension

def apSmoothGrade (L sigma gamma ell : ℝ) (dimension grade : ℕ) :
    APSmooth L sigma gamma ell dimension →ₗ[ℂ] apGrade L sigma gamma ell dimension grade where
  toFun field := field.val grade
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def apSmoothJet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (dimension : ℕ) (cell : ℤ) : APSmooth L sigma gamma ell dimension →ₗ[ℂ] ClosedJet dimension where
  toFun field := apFamilyJet field.val field.property cell
  map_add' first second := apFamilyJet_add admissible first.val second.val first.property second.property _ cell
  map_smul' scalar field := apFamilyJet_smul admissible scalar field.val field.property _ cell

theorem apSmoothJet_row {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (field : APSmooth L sigma gamma ell dimension) (grade : ℕ) (cell : ℤ) :
    apRowLinear (grade := grade) L sigma gamma ell cell (apSmoothJet admissible dimension cell field) =
      (apSmoothGrade L sigma gamma ell dimension grade field).val cell :=
  apFamilyJet_row field.val field.property grade cell

theorem apSmoothJet_ext {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (first second : APSmooth L sigma gamma ell dimension)
    (same : ∀ cell, apSmoothJet admissible dimension cell first = apSmoothJet admissible dimension cell second) : first = second := by
  apply Subtype.ext
  funext grade
  apply Subtype.ext
  apply lp.ext
  funext cell
  exact ((apSmoothJet_row admissible first grade cell).symm.trans
    (congrArg (apRowLinear (grade := grade) L sigma gamma ell cell) (same cell))).trans
      (apSmoothJet_row admissible second grade cell)

def apSmoothCoreInto (L sigma gamma ell : ℝ) (dimension : ℕ) :
    (ℤ →₀ ClosedJet dimension) →ₗ[ℂ] APSmooth L sigma gamma ell dimension where
  toFun core := ⟨fun _grade => apFiniteInto L sigma gamma ell core, fun _low _high ordered =>
    apLowering_core L sigma gamma ell ordered core⟩
  map_add' first second := by apply Subtype.ext; funext grade; exact map_add _ first second
  map_smul' scalar core := by apply Subtype.ext; funext grade; exact map_smul _ scalar core

theorem apSmoothCoreInto_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (core : ℤ →₀ ClosedJet dimension) (cell : ℤ) :
    apSmoothJet admissible dimension cell (apSmoothCoreInto L sigma gamma ell dimension core) = core cell := by
  apply closedJet_eq_of_value_eq
  rw [show (apSmoothJet admissible dimension cell (apSmoothCoreInto L sigma gamma ell dimension core)).value =
    apTrace admissible (by omega : 2 ≤ 2) cell (apFiniteInto L sigma gamma ell core) from
      apFamilyJet_value_trace admissible _ _ (by omega : 2 ≤ 2) cell, apTrace_core]

end Grad.GaugeCoefficients.Physical.Compensated
