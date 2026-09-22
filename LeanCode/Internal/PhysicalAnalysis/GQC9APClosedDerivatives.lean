import GQC8ActualSmoothCoefficient
import FP17DerivativeShift

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.Constraints

theorem apWeightedShiftL2_bound {dimension grade order : ℕ} (L sigma gamma ell : ℝ)
    (cell : ℤ) (field : ClosedJet dimension) (word : CartesianWord order) (index : CartesianMultiIndex)
    (bounded : cartesianOrder index + order ≤ grade) :
    ‖closedDerivativeL2 index (shiftedClosedJet (apWeightedJet sigma gamma ell cell field) word)‖ ≤
      ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
  change ‖closedContinuousToDiskL2 (closedMultiDerivative
    (shiftedClosedJet (apWeightedJet sigma gamma ell cell field) word) index)‖ ≤ _
  rw [shiftedClosedJet_closedMultiDerivative]
  apply apUnscaledDerivative_bound L sigma gamma ell cell field (shiftedCartesianIndex word index)
  rwa [shiftedCartesianIndex_order]

/-- Arbitrary actual weighted closed derivatives, with their exact AP2
high-grade bound. The original phase is differentiated, never replaced. -/
theorem apWeightedDerivativeSup_bound {dimension grade order : ℕ} (L sigma gamma ell : ℝ)
    (large : order + 2 ≤ grade) (cell : ℤ) (field : ClosedJet dimension) (word : CartesianWord order) :
    ‖closedDerivative (apWeightedJet sigma gamma ell cell field) order word‖ ≤
      apSupConstant * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
  let shifted := shiftedClosedJet (apWeightedJet sigma gamma ell cell field) word
  have energyBound : diskSupEnergy shifted ≤
      6 * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ ^ 2 := by
    unfold diskSupEnergy
    calc
      _ ≤ ∑ _slot : Fin 6, ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro slot _
        apply pow_le_pow_left₀ (norm_nonneg _)
        apply apWeightedShiftL2_bound L sigma gamma ell cell field word (diskSupMultiIndex slot)
        have low := diskSupMultiIndex_order_le_two slot
        omega
      _ = _ := by simp
  have squareRootBound : Real.sqrt (diskSupEnergy shifted) ≤
      Real.sqrt 6 * ‖apRowLinear (grade := grade) L sigma gamma ell cell field‖ := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · simpa only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)] using energyBound
  rw [← shiftedClosedJet_value]
  apply (ContinuousMap.norm_le _ (mul_nonneg apSupConstant_nonnegative (norm_nonneg _))).mpr
  intro point
  exact (diskSup_bound shifted point).trans
    ((mul_le_mul_of_nonneg_left squareRootBound diskSupConstant_pos.le).trans_eq (mul_assoc _ _ _).symm)

def apWeightedDerivativeCore {dimension order : ℕ} (sigma gamma ell : ℝ) (cell : ℤ)
    (word : CartesianWord order) : (ℤ →₀ ClosedJet dimension) →ₗ[ℂ] C(ClosedDisk, ComplexEuclidean dimension) where
  toFun core := closedDerivative (apWeightedJet sigma gamma ell cell (core cell)) order word
  map_add' first second := by
    change closedDerivative (apWeightedJetLinear sigma gamma ell cell (first cell + second cell)) order word = _
    rw [map_add]
    exact closedJetAdd_derivative _ _ order word
  map_smul' scalar core := by
    change closedDerivative (apWeightedJetLinear sigma gamma ell cell (scalar • core cell)) order word = _
    rw [map_smul]
    exact closedJetSmul_derivative scalar _ order word

theorem apWeightedDerivative_exists {dimension grade order : ℕ} (L sigma gamma ell : ℝ)
    (large : order + 2 ≤ grade) (cell : ℤ) (word : CartesianWord order) :
    ∃ trace : apGrade L sigma gamma ell dimension grade →L[ℂ] C(ClosedDisk, ComplexEuclidean dimension),
      (∀ core, trace (apFiniteInto L sigma gamma ell core) =
        closedDerivative (apWeightedJet sigma gamma ell cell (core cell)) order word) ∧
      (∀ field, ‖trace field‖ ≤ apSupConstant * ‖field‖) := by
  apply apDense_extension (apFiniteInto L sigma gamma ell)
    (apFiniteInto_injective L sigma gamma ell) (apFiniteInto_denseRange L sigma gamma ell)
    (apWeightedDerivativeCore sigma gamma ell cell word) apSupConstant apSupConstant_nonnegative
  intro core
  exact (apWeightedDerivativeSup_bound L sigma gamma ell large cell (core cell) word).trans
    (mul_le_mul_of_nonneg_left (by
      change ‖apRowLinear L sigma gamma ell cell (core cell)‖ ≤ ‖apFiniteEmbed (grade := grade) L sigma gamma ell core‖
      rw [← apFiniteEmbed_apply]
      exact lp.norm_apply_le_norm (by norm_num) _ _) apSupConstant_nonnegative)

def apWeightedDerivative {dimension grade order : ℕ} (L sigma gamma ell : ℝ)
    (large : order + 2 ≤ grade) (cell : ℤ) (word : CartesianWord order) :
    apGrade L sigma gamma ell dimension grade →L[ℂ] C(ClosedDisk, ComplexEuclidean dimension) :=
  (apWeightedDerivative_exists L sigma gamma ell large cell word).choose

theorem apWeightedDerivative_core {dimension grade order : ℕ} (L sigma gamma ell : ℝ)
    (large : order + 2 ≤ grade) (cell : ℤ) (word : CartesianWord order) (core : ℤ →₀ ClosedJet dimension) :
    apWeightedDerivative L sigma gamma ell large cell word (apFiniteInto L sigma gamma ell core) =
      closedDerivative (apWeightedJet sigma gamma ell cell (core cell)) order word :=
  (apWeightedDerivative_exists (dimension := dimension) L sigma gamma ell large cell word).choose_spec.1 core

theorem apWeightedDerivative_bound {dimension grade order : ℕ} (L sigma gamma ell : ℝ)
    (large : order + 2 ≤ grade) (cell : ℤ) (word : CartesianWord order)
    (field : apGrade L sigma gamma ell dimension grade) :
    ‖apWeightedDerivative L sigma gamma ell large cell word field‖ ≤ apSupConstant * ‖field‖ :=
  (apWeightedDerivative_exists L sigma gamma ell large cell word).choose_spec.2 field

end Grad.GaugeCoefficients.Physical.Compensated
