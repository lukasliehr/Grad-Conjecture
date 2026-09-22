import GC11Interface

noncomputable section

set_option maxHeartbeats 3000000

open Grad.GenericCarriers Grad.ClosedJets Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann

open Grad.GaugeCoefficients.Algebra

theorem baseCoefficient_ext {L sigma gamma ell : ℝ} {dimension : ℕ}
    {first second : BaseCoefficient L sigma gamma ell dimension}
    (equalValue : ∀ (cell : ℤ) (point : ClosedDisk),
      coefficientValue first cell point = coefficientValue second cell point) :
    first = second := by
  apply Subtype.ext
  apply Subtype.ext
  funext pair
  rcases pair with ⟨cell, index⟩
  rw [derivativeIndex_zero_eq index]
  apply ContinuousMap.ext
  intro point
  calc
    first.1 (cell, zeroDerivativeIndex) point =
        (coefficientScale L sigma gamma ell 0 cell zeroDerivativeIndex point : ℂ) •
          coefficientValue first cell point :=
      weighted_derivative_literal 0 dimension dimension first cell zeroDerivativeIndex point
    _ = (coefficientScale L sigma gamma ell 0 cell zeroDerivativeIndex point : ℂ) •
          coefficientValue second cell point := by rw [equalValue cell point]
    _ = second.1 (cell, zeroDerivativeIndex) point :=
      (weighted_derivative_literal 0 dimension dimension second cell
        zeroDerivativeIndex point).symm

theorem coefficientComposition_add_outer {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (first second inner : BaseCoefficient L sigma gamma ell dimension) :
    coefficientComposition admissible 0 (first + second) inner =
      coefficientComposition admissible 0 first inner +
        coefficientComposition admissible 0 second inner := by
  apply Subtype.ext
  exact rawComposition_add_outer admissible 0 first.1 second.1 inner.1

theorem coefficientComposition_add_inner {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (outer first second : BaseCoefficient L sigma gamma ell dimension) :
    coefficientComposition admissible 0 outer (first + second) =
      coefficientComposition admissible 0 outer first +
        coefficientComposition admissible 0 outer second := by
  apply Subtype.ext
  exact rawComposition_add_inner admissible 0 outer.1 first.1 second.1

theorem coefficientComposition_smul_outer {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (scalar : ℂ) (outer inner : BaseCoefficient L sigma gamma ell dimension) :
    coefficientComposition admissible 0 (scalar • outer) inner =
      scalar • coefficientComposition admissible 0 outer inner := by
  apply Subtype.ext
  exact rawComposition_smul_outer admissible 0 scalar outer.1 inner.1

theorem coefficientComposition_smul_inner {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (scalar : ℂ) (outer inner : BaseCoefficient L sigma gamma ell dimension) :
    coefficientComposition admissible 0 outer (scalar • inner) =
      scalar • coefficientComposition admissible 0 outer inner := by
  apply Subtype.ext
  exact rawComposition_smul_inner admissible 0 scalar outer.1 inner.1

theorem coefficientComposition_zero_outer {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (inner : BaseCoefficient L sigma gamma ell dimension) :
    coefficientComposition admissible 0
        (0 : BaseCoefficient L sigma gamma ell dimension) inner = 0 := by
  apply Subtype.ext
  exact rawComposition_zero_outer admissible 0 inner.1

theorem coefficientComposition_zero_inner {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (outer : BaseCoefficient L sigma gamma ell dimension) :
    coefficientComposition admissible 0 outer
        (0 : BaseCoefficient L sigma gamma ell dimension) = 0 := by
  apply Subtype.ext
  exact rawComposition_zero_inner admissible 0 outer.1

theorem coefficientComposition_identity_left {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (coefficient : BaseCoefficient L sigma gamma ell dimension) :
    coefficientComposition admissible 0
        (identityCoefficient L sigma gamma ell dimension) coefficient = coefficient := by
  apply baseCoefficient_ext
  intro cell point
  rw [coefficientComposition_value]
  rw [tsum_eq_single 0]
  · rw [identityCoefficient_value, if_pos rfl]
    simp
  · intro first different
    rw [identityCoefficient_value, if_neg different]
    apply ContinuousLinearMap.ext
    intro value
    simp

theorem coefficientComposition_identity_right {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (coefficient : BaseCoefficient L sigma gamma ell dimension) :
    coefficientComposition admissible 0 coefficient
        (identityCoefficient L sigma gamma ell dimension) = coefficient := by
  apply baseCoefficient_ext
  intro cell point
  rw [coefficientComposition_value]
  rw [tsum_eq_single cell]
  · rw [identityCoefficient_value, if_pos (by omega)]
    simp
  · intro first different
    have nonzero : cell - first ≠ 0 := by omega
    rw [identityCoefficient_value, if_neg nonzero]
    apply ContinuousLinearMap.ext
    intro value
    simp

def baseCompositionLeftLinear {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (inner : BaseCoefficient L sigma gamma ell dimension) :
    BaseCoefficient L sigma gamma ell dimension →ₗ[ℂ]
      BaseCoefficient L sigma gamma ell dimension where
  toFun outer := coefficientComposition admissible 0 outer inner
  map_add' first second := coefficientComposition_add_outer admissible first second inner
  map_smul' scalar outer := coefficientComposition_smul_outer admissible scalar outer inner

def baseCompositionLeft {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (inner : BaseCoefficient L sigma gamma ell dimension) :
    BaseCoefficient L sigma gamma ell dimension →L[ℂ]
      BaseCoefficient L sigma gamma ell dimension :=
  (baseCompositionLeftLinear admissible inner).mkContinuous ‖inner‖ (fun outer => by
    change ‖coefficientComposition admissible 0 outer inner‖ ≤ ‖inner‖ * ‖outer‖
    simpa only [mul_comm] using coefficientComposition_base_norm_le admissible outer inner)

def baseCompositionRightLinear {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (outer : BaseCoefficient L sigma gamma ell dimension) :
    BaseCoefficient L sigma gamma ell dimension →ₗ[ℂ]
      BaseCoefficient L sigma gamma ell dimension where
  toFun inner := coefficientComposition admissible 0 outer inner
  map_add' first second := coefficientComposition_add_inner admissible outer first second
  map_smul' scalar inner := coefficientComposition_smul_inner admissible scalar outer inner

def baseCompositionRight {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (outer : BaseCoefficient L sigma gamma ell dimension) :
    BaseCoefficient L sigma gamma ell dimension →L[ℂ]
      BaseCoefficient L sigma gamma ell dimension :=
  (baseCompositionRightLinear admissible outer).mkContinuous ‖outer‖ (fun inner => by
    exact coefficientComposition_base_norm_le admissible outer inner)

@[simp] theorem baseCompositionLeft_apply {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (inner outer : BaseCoefficient L sigma gamma ell dimension) :
    baseCompositionLeft admissible inner outer =
      coefficientComposition admissible 0 outer inner := rfl

@[simp] theorem baseCompositionRight_apply {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (outer inner : BaseCoefficient L sigma gamma ell dimension) :
    baseCompositionRight admissible outer inner =
      coefficientComposition admissible 0 outer inner := rfl

end Grad.GaugeCoefficients.Neumann
