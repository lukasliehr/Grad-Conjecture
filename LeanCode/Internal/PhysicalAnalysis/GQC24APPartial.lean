import GQC23PartialRowBound

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope

theorem apPartialFinite_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension grade : ℕ} (coordinate : Fin 2) (core : ℤ →₀ ClosedJet dimension) :
    ‖apFiniteInto (grade := grade) L sigma gamma ell (apFiniteJetMap (partialJetLinear dimension coordinate) core)‖ ≤
      partialRowConstant L gamma grade * ‖apFiniteInto (grade := grade + 1) L sigma gamma ell core‖ := by
  change ‖apFiniteEmbed (grade := grade) L sigma gamma ell (apFiniteJetMap (partialJetLinear dimension coordinate) core)‖ ≤
    partialRowConstant L gamma grade * ‖apFiniteEmbed (grade := grade + 1) L sigma gamma ell core‖
  calc
    _ ≤ ‖(partialRowConstant L gamma grade : ℂ) • apFiniteEmbed (grade := grade + 1) L sigma gamma ell core‖ := by
      apply lp.norm_mono (by norm_num)
      intro cell
      rw [apFiniteEmbed_apply, apFiniteJetMap_apply]
      change _ ≤ ‖(partialRowConstant L gamma grade : ℂ) • apFiniteEmbed (grade := grade + 1) L sigma gamma ell core cell‖
      rw [apFiniteEmbed_apply, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (partialRowConstant_nonnegative admissible grade)]
      exact partialRow_bound admissible cell coordinate (core cell)
    _ = _ := by rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (partialRowConstant_nonnegative admissible grade)]

theorem apPartial_exists {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (dimension grade : ℕ) (coordinate : Fin 2) :
    ∃ mapping : apGrade L sigma gamma ell dimension (grade + 1) →L[ℂ] apGrade L sigma gamma ell dimension grade,
      (∀ core, mapping (apFiniteInto L sigma gamma ell core) =
        apFiniteInto L sigma gamma ell (apFiniteJetMap (partialJetLinear dimension coordinate) core)) ∧
      (∀ field, ‖mapping field‖ ≤ partialRowConstant L gamma grade * ‖field‖) :=
  apDense_extension (apFiniteInto (grade := grade + 1) L sigma gamma ell)
    (apFiniteInto_injective L sigma gamma ell) (apFiniteInto_denseRange L sigma gamma ell)
    ((apFiniteInto (grade := grade) L sigma gamma ell).comp (apFiniteJetMap (partialJetLinear dimension coordinate)))
    (partialRowConstant L gamma grade) (partialRowConstant_nonnegative admissible grade)
    (apPartialFinite_bound admissible coordinate)

def apPartial {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (dimension grade : ℕ) (coordinate : Fin 2) :
    apGrade L sigma gamma ell dimension (grade + 1) →L[ℂ] apGrade L sigma gamma ell dimension grade :=
  (apPartial_exists admissible dimension grade coordinate).choose

theorem apPartial_core {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (dimension grade : ℕ) (coordinate : Fin 2) (core : ℤ →₀ ClosedJet dimension) :
    apPartial admissible dimension grade coordinate (apFiniteInto L sigma gamma ell core) =
      apFiniteInto L sigma gamma ell (apFiniteJetMap (partialJetLinear dimension coordinate) core) :=
  (apPartial_exists admissible dimension grade coordinate).choose_spec.1 core

theorem apPartial_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (dimension grade : ℕ) (coordinate : Fin 2) (field : apGrade L sigma gamma ell dimension (grade + 1)) :
    ‖apPartial admissible dimension grade coordinate field‖ ≤ partialRowConstant L gamma grade * ‖field‖ :=
  (apPartial_exists admissible dimension grade coordinate).choose_spec.2 field

theorem apPartial_lowering {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension low high : ℕ} (ordered : low ≤ high) (coordinate : Fin 2)
    (field : apGrade L sigma gamma ell dimension (high + 1)) :
    apLowering L sigma gamma ell ordered (apPartial admissible dimension high coordinate field) =
      apPartial admissible dimension low coordinate
        (apLowering L sigma gamma ell (Nat.add_le_add_right ordered 1) field) := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := high + 1) L sigma gamma ell)
    (isClosed_eq ((apLowering L sigma gamma ell ordered).continuous.comp
      (apPartial admissible dimension high coordinate).continuous)
      ((apPartial admissible dimension low coordinate).continuous.comp
        (apLowering L sigma gamma ell (Nat.add_le_add_right ordered 1)).continuous)) _ field
  intro core
  simp only [Function.comp_apply]
  rw [apPartial_core, apLowering_core, apLowering_core, apPartial_core]

def apSmoothPartial {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (dimension : ℕ) (coordinate : Fin 2) : APSmooth L sigma gamma ell dimension →ₗ[ℂ] APSmooth L sigma gamma ell dimension where
  toFun field := ⟨fun grade => apPartial admissible dimension grade coordinate (field.val (grade + 1)),
    fun low high ordered => by
      rw [apPartial_lowering, field.property (low + 1) (high + 1) (Nat.add_le_add_right ordered 1)]⟩
  map_add' first second := by
    apply Subtype.ext
    funext grade
    exact (apPartial admissible dimension grade coordinate).map_add (first.val (grade + 1)) (second.val (grade + 1))
  map_smul' scalar field := by
    apply Subtype.ext
    funext grade
    exact (apPartial admissible dimension grade coordinate).map_smul scalar (field.val (grade + 1))

end Grad.GaugeCoefficients.Physical.Compensated
