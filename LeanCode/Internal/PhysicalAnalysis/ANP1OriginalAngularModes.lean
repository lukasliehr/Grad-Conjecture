import GQD10FaithfulConsumer
import GC21Consumer

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.RawCircularSectors

open Grad.GaugeCoefficients.Physical.Compensated
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem apAngularMode_exists (L sigma gamma ell : ℝ) (dimension grade : ℕ) (mode : ℤ) :
    ∃ completed : apGrade L sigma gamma ell dimension grade →L[ℂ]
        apGrade L sigma gamma ell dimension grade,
      (∀ core, completed (apFiniteInto L sigma gamma ell core) =
        apFiniteInto L sigma gamma ell (apFiniteJetMap (angularClosedJetLinear dimension mode) core)) ∧
      (∀ field, ‖completed field‖ ≤ orthogonalGradeConstant grade * ‖field‖) :=
  apDense_extension (apFiniteInto L sigma gamma ell)
    (apFiniteInto_injective L sigma gamma ell) (apFiniteInto_denseRange L sigma gamma ell)
    ((apFiniteInto L sigma gamma ell).comp (apFiniteJetMap (angularClosedJetLinear dimension mode)))
    (orthogonalGradeConstant grade) (orthogonalGradeConstant_nonnegative grade)
    (apFiniteJetMap_bound L sigma gamma ell _ _ (orthogonalGradeConstant_nonnegative grade)
      (fun cell field => apAngular_row_bound L sigma gamma ell cell mode field))

def apAngularMode (L sigma gamma ell : ℝ) (dimension grade : ℕ) (mode : ℤ) :
    apGrade L sigma gamma ell dimension grade →L[ℂ] apGrade L sigma gamma ell dimension grade :=
  (apAngularMode_exists L sigma gamma ell dimension grade mode).choose

theorem apAngularMode_core (L sigma gamma ell : ℝ) (dimension grade : ℕ) (mode : ℤ)
    (core : ℤ →₀ ClosedJet dimension) :
    apAngularMode L sigma gamma ell dimension grade mode (apFiniteInto L sigma gamma ell core) =
      apFiniteInto L sigma gamma ell (apFiniteJetMap (angularClosedJetLinear dimension mode) core) :=
  (apAngularMode_exists L sigma gamma ell dimension grade mode).choose_spec.1 core

theorem apAngularMode_bound (L sigma gamma ell : ℝ) (dimension grade : ℕ) (mode : ℤ)
    (field : apGrade L sigma gamma ell dimension grade) :
    ‖apAngularMode L sigma gamma ell dimension grade mode field‖ ≤ orthogonalGradeConstant grade * ‖field‖ :=
  (apAngularMode_exists L sigma gamma ell dimension grade mode).choose_spec.2 field

theorem apAngularMode_lowering (L sigma gamma ell : ℝ) (dimension : ℕ) (mode : ℤ)
    {low high : ℕ} (ordered : low ≤ high) (field : apGrade L sigma gamma ell dimension high) :
    apLowering L sigma gamma ell ordered (apAngularMode L sigma gamma ell dimension high mode field) =
      apAngularMode L sigma gamma ell dimension low mode (apLowering L sigma gamma ell ordered field) := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := high) L sigma gamma ell)
    (isClosed_eq ((apLowering L sigma gamma ell ordered).continuous.comp
      (apAngularMode L sigma gamma ell dimension high mode).continuous)
      ((apAngularMode L sigma gamma ell dimension low mode).continuous.comp
        (apLowering L sigma gamma ell ordered).continuous)) _ field
  intro core
  simp only [Function.comp_apply]
  rw [apAngularMode_core, apLowering_core, apLowering_core, apAngularMode_core]

def apSmoothAngularMode (L sigma gamma ell : ℝ) (dimension : ℕ) (mode : ℤ) :
    APSmooth L sigma gamma ell dimension →ₗ[ℂ] APSmooth L sigma gamma ell dimension :=
  apSmoothMap (fun grade => apAngularMode L sigma gamma ell dimension grade mode)
    (fun _low _high ordered field => apAngularMode_lowering L sigma gamma ell dimension mode ordered field)


end Grad.RawCircularSectors
