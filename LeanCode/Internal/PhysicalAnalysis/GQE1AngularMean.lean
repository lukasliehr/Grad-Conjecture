import GQD10FaithfulConsumer
import GC21Consumer

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem norm_sub_bounded_map {E : Type*} [SeminormedAddCommGroup E]
    (field image : E) (constant : ℝ) (bound : ‖image‖ ≤ constant * ‖field‖) :
    ‖field - image‖ ≤ (1 + constant) * ‖field‖ := by
  calc
    _ ≤ ‖field‖ + ‖image‖ := norm_sub_le field image
    _ ≤ ‖field‖ + constant * ‖field‖ := add_le_add le_rfl bound
    _ = _ := by ring

theorem apAngularMean_exists (L sigma gamma ell : ℝ) (dimension grade : ℕ) :
    ∃ completed : apGrade L sigma gamma ell dimension grade →L[ℂ]
        apGrade L sigma gamma ell dimension grade,
      (∀ core, completed (apFiniteInto L sigma gamma ell core) =
        apFiniteInto L sigma gamma ell (apFiniteJetMap (angularClosedJetLinear dimension 0) core)) ∧
      (∀ field, ‖completed field‖ ≤ orthogonalGradeConstant grade * ‖field‖) :=
  apDense_extension (apFiniteInto L sigma gamma ell)
    (apFiniteInto_injective L sigma gamma ell) (apFiniteInto_denseRange L sigma gamma ell)
    ((apFiniteInto L sigma gamma ell).comp (apFiniteJetMap (angularClosedJetLinear dimension 0)))
    (orthogonalGradeConstant grade) (orthogonalGradeConstant_nonnegative grade)
    (apFiniteJetMap_bound L sigma gamma ell _ _ (orthogonalGradeConstant_nonnegative grade)
      (fun cell field => apAngular_row_bound L sigma gamma ell cell 0 field))

def apAngularMean (L sigma gamma ell : ℝ) (dimension grade : ℕ) :
    apGrade L sigma gamma ell dimension grade →L[ℂ] apGrade L sigma gamma ell dimension grade :=
  (apAngularMean_exists L sigma gamma ell dimension grade).choose

theorem apAngularMean_core (L sigma gamma ell : ℝ) (dimension grade : ℕ)
    (core : ℤ →₀ ClosedJet dimension) :
    apAngularMean L sigma gamma ell dimension grade (apFiniteInto L sigma gamma ell core) =
      apFiniteInto L sigma gamma ell (apFiniteJetMap (angularClosedJetLinear dimension 0) core) :=
  (apAngularMean_exists L sigma gamma ell dimension grade).choose_spec.1 core

theorem apAngularMean_bound (L sigma gamma ell : ℝ) (dimension grade : ℕ)
    (field : apGrade L sigma gamma ell dimension grade) :
    ‖apAngularMean L sigma gamma ell dimension grade field‖ ≤ orthogonalGradeConstant grade * ‖field‖ :=
  (apAngularMean_exists L sigma gamma ell dimension grade).choose_spec.2 field

theorem apAngularMean_lowering (L sigma gamma ell : ℝ) (dimension : ℕ)
    {low high : ℕ} (ordered : low ≤ high) (field : apGrade L sigma gamma ell dimension high) :
    apLowering L sigma gamma ell ordered (apAngularMean L sigma gamma ell dimension high field) =
      apAngularMean L sigma gamma ell dimension low (apLowering L sigma gamma ell ordered field) := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := high) L sigma gamma ell)
    (isClosed_eq ((apLowering L sigma gamma ell ordered).continuous.comp
      (apAngularMean L sigma gamma ell dimension high).continuous)
      ((apAngularMean L sigma gamma ell dimension low).continuous.comp
        (apLowering L sigma gamma ell ordered).continuous)) _ field
  intro core
  simp only [Function.comp_apply]
  rw [apAngularMean_core, apLowering_core, apLowering_core, apAngularMean_core]

def apSmoothAngularMean (L sigma gamma ell : ℝ) (dimension : ℕ) :
    APSmooth L sigma gamma ell dimension →ₗ[ℂ] APSmooth L sigma gamma ell dimension :=
  apSmoothMap (apAngularMean L sigma gamma ell dimension)
    (fun _low _high ordered field => apAngularMean_lowering L sigma gamma ell dimension ordered field)

def apMeanFree (L sigma gamma ell : ℝ) (dimension grade : ℕ) :
    apGrade L sigma gamma ell dimension grade →L[ℂ] apGrade L sigma gamma ell dimension grade :=
  ContinuousLinearMap.id ℂ _ - apAngularMean L sigma gamma ell dimension grade

theorem apMeanFree_bound (L sigma gamma ell : ℝ) (dimension grade : ℕ)
    (field : apGrade L sigma gamma ell dimension grade) :
    ‖apMeanFree L sigma gamma ell dimension grade field‖ ≤
      (1 + orthogonalGradeConstant grade) * ‖field‖ := by
  change ‖field - apAngularMean L sigma gamma ell dimension grade field‖ ≤ _
  exact norm_sub_bounded_map field (apAngularMean L sigma gamma ell dimension grade field)
    (orthogonalGradeConstant grade) (apAngularMean_bound L sigma gamma ell dimension grade field)

end Grad.GaugeCoefficients.Physical.Compensated
