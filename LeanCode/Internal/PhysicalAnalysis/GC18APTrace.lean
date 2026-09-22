import GC18APSupBound
import GC18DenseExtension

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.GaugeCoefficients.Algebra

def apWeightedCoreTrace {dimension : ℕ} (sigma gamma ell : ℝ) (cell : ℤ) :
    (ℤ →₀ ClosedJet dimension) →ₗ[ℂ] C(ClosedDisk, ComplexEuclidean dimension) where
  toFun field := (apWeightedJet sigma gamma ell cell (field cell)).value
  map_add' first second := by
    change (apWeightedJetLinear sigma gamma ell cell (first cell + second cell)).value = _
    rw [map_add]
    rfl
  map_smul' scalar field := by
    change (apWeightedJetLinear sigma gamma ell cell (scalar • field cell)).value = _
    rw [map_smul]
    rfl

theorem apWeightedTrace_exists {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (large : 2 ≤ grade) (cell : ℤ) :
    ∃ trace : apGrade L sigma gamma ell dimension grade →L[ℂ] C(ClosedDisk, ComplexEuclidean dimension),
      (∀ core, trace (apFiniteInto L sigma gamma ell core) = (apWeightedJet sigma gamma ell cell (core cell)).value) ∧
      (∀ field, ‖trace field‖ ≤ apSupConstant * ‖field‖) := by
  apply apDense_extension (apFiniteInto L sigma gamma ell)
    (apFiniteInto_injective L sigma gamma ell) (apFiniteInto_denseRange L sigma gamma ell)
    (apWeightedCoreTrace sigma gamma ell cell) apSupConstant apSupConstant_nonnegative
  intro core
  exact (apWeightedSup_bound L sigma gamma ell large cell (core cell)).trans
    (mul_le_mul_of_nonneg_left (by
      change ‖apRowLinear L sigma gamma ell cell (core cell)‖ ≤ ‖apFiniteEmbed (grade := grade) L sigma gamma ell core‖
      rw [← apFiniteEmbed_apply]
      exact lp.norm_apply_le_norm (by norm_num) _ _) apSupConstant_nonnegative)

def apWeightedTrace {dimension grade : ℕ} (L sigma gamma ell : ℝ) (large : 2 ≤ grade) (cell : ℤ) :
    apGrade L sigma gamma ell dimension grade →L[ℂ] C(ClosedDisk, ComplexEuclidean dimension) :=
  (apWeightedTrace_exists L sigma gamma ell large cell).choose

theorem apWeightedTrace_core {dimension grade : ℕ} (L sigma gamma ell : ℝ) (large : 2 ≤ grade) (cell : ℤ)
    (core : ℤ →₀ ClosedJet dimension) :
    apWeightedTrace L sigma gamma ell large cell (apFiniteInto L sigma gamma ell core) =
      (apWeightedJet sigma gamma ell cell (core cell)).value :=
  (apWeightedTrace_exists L sigma gamma ell large cell).choose_spec.1 core

theorem apWeightedTrace_bound {dimension grade : ℕ} (L sigma gamma ell : ℝ) (large : 2 ≤ grade) (cell : ℤ)
    (field : apGrade L sigma gamma ell dimension grade) :
    ‖apWeightedTrace L sigma gamma ell large cell field‖ ≤ apSupConstant * ‖field‖ :=
  (apWeightedTrace_exists L sigma gamma ell large cell).choose_spec.2 field

theorem apWeightedTrace_l2 {dimension grade : ℕ} (L sigma gamma ell : ℝ) (large : 2 ≤ grade) (cell : ℤ)
    (field : apGrade L sigma gamma ell dimension grade) :
    closedValueL2Continuous dimension (apWeightedTrace L sigma gamma ell large cell field) =
      apUnscaledCoordinate L sigma gamma ell cell (zeroGradeIndex grade) field := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := grade) L sigma gamma ell)
    (isClosed_eq ((closedValueL2Continuous dimension).continuous.comp (apWeightedTrace L sigma gamma ell large cell).continuous)
      (apUnscaledCoordinate L sigma gamma ell cell (zeroGradeIndex grade)).continuous) _ field
  intro core
  simp only [Function.comp_apply]
  rw [apWeightedTrace_core, apUnscaledCoordinate_core]
  change closedContinuousToDiskL2 _ = closedContinuousToDiskL2 (closedMultiDerivative _ (0, 0))
  rw [closedMultiDerivative_zero]

theorem apWeightedTrace_ext {dimension grade : ℕ} (L sigma gamma ell : ℝ) (large : 2 ≤ grade)
    (first second : apGrade L sigma gamma ell dimension grade)
    (equality : ∀ cell, apWeightedTrace L sigma gamma ell large cell first = apWeightedTrace L sigma gamma ell large cell second) :
    first = second := by
  apply apGrade_ext L sigma gamma ell
  intro cell
  rw [← apWeightedTrace_l2 L sigma gamma ell large, ← apWeightedTrace_l2 L sigma gamma ell large, equality]

end Grad.GaugeCoefficients.Physical.RadialLedger
