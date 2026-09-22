import GQC25APPartialRealization

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope

theorem apValueMap_exists {input output : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) :
    ∃ completed : apGrade L sigma gamma ell input grade →L[ℂ] apGrade L sigma gamma ell output grade,
      (∀ core, completed (apFiniteInto L sigma gamma ell core) =
        apFiniteInto L sigma gamma ell (apFiniteJetMap (valueMapJetLinear input output mapping) core)) ∧
      (∀ field, ‖completed field‖ ≤ ‖mapping‖ * ‖field‖) :=
  apDense_extension (apFiniteInto L sigma gamma ell)
    (apFiniteInto_injective L sigma gamma ell) (apFiniteInto_denseRange L sigma gamma ell)
    ((apFiniteInto L sigma gamma ell).comp (apFiniteJetMap (valueMapJetLinear input output mapping)))
    ‖mapping‖ (norm_nonneg _) (apFiniteJetMap_bound L sigma gamma ell _ ‖mapping‖ (norm_nonneg _)
      (fun cell field => apValueMap_row_bound L sigma gamma ell cell mapping field))

def apValueMap {input output : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) :
    apGrade L sigma gamma ell input grade →L[ℂ] apGrade L sigma gamma ell output grade :=
  (apValueMap_exists L sigma gamma ell grade mapping).choose

theorem apValueMap_core {input output : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) (core : ℤ →₀ ClosedJet input) :
    apValueMap L sigma gamma ell grade mapping (apFiniteInto L sigma gamma ell core) =
      apFiniteInto L sigma gamma ell (apFiniteJetMap (valueMapJetLinear input output mapping) core) :=
  (apValueMap_exists L sigma gamma ell grade mapping).choose_spec.1 core

theorem apValueMap_bound {input output : ℕ} (L sigma gamma ell : ℝ) (grade : ℕ)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) (field : apGrade L sigma gamma ell input grade) :
    ‖apValueMap L sigma gamma ell grade mapping field‖ ≤ ‖mapping‖ * ‖field‖ :=
  (apValueMap_exists L sigma gamma ell grade mapping).choose_spec.2 field

theorem apValueMap_lowering {input output low high : ℕ} (L sigma gamma ell : ℝ) (ordered : low ≤ high)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) (field : apGrade L sigma gamma ell input high) :
    apLowering L sigma gamma ell ordered (apValueMap L sigma gamma ell high mapping field) =
      apValueMap L sigma gamma ell low mapping (apLowering L sigma gamma ell ordered field) := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := input) (grade := high) L sigma gamma ell)
    (isClosed_eq ((apLowering L sigma gamma ell ordered).continuous.comp
      (apValueMap L sigma gamma ell high mapping).continuous)
      ((apValueMap L sigma gamma ell low mapping).continuous.comp (apLowering L sigma gamma ell ordered).continuous)) _ field
  intro core
  simp only [Function.comp_apply]
  rw [apValueMap_core, apLowering_core, apLowering_core, apValueMap_core]

def apSmoothValueMap {input output : ℕ} (L sigma gamma ell : ℝ)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) :
    APSmooth L sigma gamma ell input →ₗ[ℂ] APSmooth L sigma gamma ell output :=
  apSmoothMap (fun grade => apValueMap L sigma gamma ell grade mapping)
    (fun _low _high ordered field => apValueMap_lowering L sigma gamma ell ordered mapping field)

theorem apValueMap_trace {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output grade : ℕ} (large : 2 ≤ grade) (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (field : apGrade L sigma gamma ell input grade) (cell : ℤ) (point : ClosedDisk) :
    apTrace admissible large cell (apValueMap L sigma gamma ell grade mapping field) point =
      mapping (apTrace admissible large cell field point) := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := input) (grade := grade) L sigma gamma ell)
    (isClosed_eq ((ContinuousMap.evalCLM ℂ point).continuous.comp
      ((apTrace admissible large cell).continuous.comp (apValueMap L sigma gamma ell grade mapping).continuous))
      (mapping.continuous.comp ((ContinuousMap.evalCLM ℂ point).continuous.comp (apTrace admissible large cell).continuous))) _ field
  intro core
  simp only [Function.comp_apply]
  rw [apValueMap_core, apTrace_core, apTrace_core]
  exact valueMapJet_value mapping (core cell) point

theorem apSmoothValueMap_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (field : APSmooth L sigma gamma ell input) (cell : ℤ) :
    apSmoothJet admissible output cell (apSmoothValueMap L sigma gamma ell mapping field) =
      valueMapJet mapping (apSmoothJet admissible input cell field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [valueMapJet_value]
  change (apFamilyJet (apSmoothValueMap L sigma gamma ell mapping field).val _ cell).value point =
    mapping ((apFamilyJet field.val field.property cell).value point)
  rw [apFamilyJet_value_trace admissible (apSmoothValueMap L sigma gamma ell mapping field).val
    (apSmoothValueMap L sigma gamma ell mapping field).property (by omega : 2 ≤ 2) cell,
    apFamilyJet_value_trace admissible field.val field.property (by omega : 2 ≤ 2) cell]
  exact apValueMap_trace admissible (by omega : 2 ≤ 2) mapping (field.val 2) cell point

end Grad.GaugeCoefficients.Physical.Compensated
