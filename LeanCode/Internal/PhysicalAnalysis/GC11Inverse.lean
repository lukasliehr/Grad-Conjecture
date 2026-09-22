import GC11Powers

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

open Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann

open Grad.GaugeCoefficients.Algebra

theorem coefficientComposition_sub_outer {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (first second inner : BaseCoefficient L sigma gamma ell dimension) :
    coefficientComposition admissible 0 (first - second) inner =
      coefficientComposition admissible 0 first inner -
        coefficientComposition admissible 0 second inner := by
  rw [sub_eq_add_neg, sub_eq_add_neg,
    coefficientComposition_add_outer]
  have negIdentity : -second = (-1 : ℂ) • second := by simp
  rw [negIdentity, coefficientComposition_smul_outer]
  simp

theorem coefficientComposition_sub_inner {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (outer first second : BaseCoefficient L sigma gamma ell dimension) :
    coefficientComposition admissible 0 outer (first - second) =
      coefficientComposition admissible 0 outer first -
        coefficientComposition admissible 0 outer second := by
  rw [sub_eq_add_neg, sub_eq_add_neg,
    coefficientComposition_add_inner]
  have negIdentity : -second = (-1 : ℂ) • second := by simp
  rw [negIdentity, coefficientComposition_smul_inner]
  simp

theorem coefficientNeumannInverse_eq_identity_add_tail {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (positive : 0 < dimension)
    (coefficient : BaseCoefficient L sigma gamma ell dimension) (theta : ℝ)
    (normBound : ‖coefficient‖ ≤ theta) (thetaLt : theta < 1) :
    coefficientNeumannInverse admissible coefficient =
      identityCoefficient L sigma gamma ell dimension +
        ∑' power : ℕ, coefficientPower admissible coefficient (power + 1) := by
  unfold coefficientNeumannInverse
  rw [(coefficientPower_summable admissible positive coefficient theta
    normBound thetaLt).tsum_eq_zero_add]
  rw [coefficientPower_zero]

theorem coefficient_mul_neumannInverse {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (positive : 0 < dimension)
    (coefficient : BaseCoefficient L sigma gamma ell dimension) (theta : ℝ)
    (normBound : ‖coefficient‖ ≤ theta) (thetaLt : theta < 1) :
    coefficientComposition admissible 0 coefficient
        (coefficientNeumannInverse admissible coefficient) =
      ∑' power : ℕ, coefficientPower admissible coefficient (power + 1) := by
  let multiplication := baseCompositionRight admissible coefficient
  have summable := coefficientPower_summable admissible positive coefficient theta
    normBound thetaLt
  unfold coefficientNeumannInverse
  change multiplication (∑' power : ℕ, coefficientPower admissible coefficient power) = _
  rw [multiplication.map_tsum summable]
  apply tsum_congr
  intro power
  exact coefficientPower_succ admissible coefficient power

theorem neumannInverse_mul_coefficient {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (positive : 0 < dimension)
    (coefficient : BaseCoefficient L sigma gamma ell dimension) (theta : ℝ)
    (normBound : ‖coefficient‖ ≤ theta) (thetaLt : theta < 1) :
    coefficientComposition admissible 0
        (coefficientNeumannInverse admissible coefficient) coefficient =
      ∑' power : ℕ, coefficientPower admissible coefficient (power + 1) := by
  let multiplication := baseCompositionLeft admissible coefficient
  have summable := coefficientPower_summable admissible positive coefficient theta
    normBound thetaLt
  unfold coefficientNeumannInverse
  change multiplication (∑' power : ℕ, coefficientPower admissible coefficient power) = _
  rw [multiplication.map_tsum summable]
  apply tsum_congr
  intro power
  exact coefficientPower_succ_right admissible coefficient power

theorem coefficientNeumannInverse_left_identity {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (positive : 0 < dimension)
    (coefficient : BaseCoefficient L sigma gamma ell dimension) (theta : ℝ)
    (normBound : ‖coefficient‖ ≤ theta) (thetaLt : theta < 1) :
    coefficientComposition admissible 0
        (identityCoefficient L sigma gamma ell dimension - coefficient)
        (coefficientNeumannInverse admissible coefficient) =
      identityCoefficient L sigma gamma ell dimension := by
  rw [coefficientComposition_sub_outer,
    coefficientComposition_identity_left,
    coefficient_mul_neumannInverse admissible positive coefficient theta normBound thetaLt,
    coefficientNeumannInverse_eq_identity_add_tail admissible positive coefficient theta
      normBound thetaLt]
  abel

theorem coefficientNeumannInverse_right_identity {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (positive : 0 < dimension)
    (coefficient : BaseCoefficient L sigma gamma ell dimension) (theta : ℝ)
    (normBound : ‖coefficient‖ ≤ theta) (thetaLt : theta < 1) :
    coefficientComposition admissible 0
        (coefficientNeumannInverse admissible coefficient)
        (identityCoefficient L sigma gamma ell dimension - coefficient) =
      identityCoefficient L sigma gamma ell dimension := by
  rw [coefficientComposition_sub_inner,
    coefficientComposition_identity_right,
    neumannInverse_mul_coefficient admissible positive coefficient theta normBound thetaLt,
    coefficientNeumannInverse_eq_identity_add_tail admissible positive coefficient theta
      normBound thetaLt]
  abel

end Grad.GaugeCoefficients.Neumann
