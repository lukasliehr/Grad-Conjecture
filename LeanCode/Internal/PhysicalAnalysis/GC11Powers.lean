import GC11Associativity

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

open Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann

open Grad.GaugeCoefficients.Algebra

noncomputable instance baseCoefficientCompleteSpace
    (L sigma gamma ell : ℝ) (dimension : ℕ) :
    CompleteSpace (BaseCoefficient L sigma gamma ell dimension) :=
  completeSpace_of_isComplete_univ
    (coefficient_complete 0 dimension dimension)

@[simp] theorem coefficientPower_zero {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (coefficient : BaseCoefficient L sigma gamma ell dimension) :
    coefficientPower admissible coefficient 0 =
      identityCoefficient L sigma gamma ell dimension := rfl

@[simp] theorem coefficientPower_succ {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (coefficient : BaseCoefficient L sigma gamma ell dimension) (power : ℕ) :
    coefficientPower admissible coefficient (power + 1) =
      coefficientComposition admissible 0 coefficient
        (coefficientPower admissible coefficient power) := rfl

theorem coefficientPower_succ_right {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (coefficient : BaseCoefficient L sigma gamma ell dimension) (power : ℕ) :
    coefficientComposition admissible 0
        (coefficientPower admissible coefficient power) coefficient =
      coefficientPower admissible coefficient (power + 1) := by
  induction power with
  | zero =>
      rw [coefficientPower_zero, coefficientPower_succ,
        coefficientPower_zero, coefficientComposition_identity_left,
        coefficientComposition_identity_right]
  | succ power inductionHypothesis =>
      rw [coefficientPower_succ, coefficientPower_succ]
      rw [coefficientComposition_associative, inductionHypothesis]

theorem coefficientPower_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (positive : 0 < dimension)
    (coefficient : BaseCoefficient L sigma gamma ell dimension) (power : ℕ) :
    ‖coefficientPower admissible coefficient power‖ ≤ ‖coefficient‖ ^ power := by
  induction power with
  | zero =>
      rw [coefficientPower_zero, pow_zero,
        identityCoefficient_norm L sigma gamma ell dimension positive]
  | succ power inductionHypothesis =>
      rw [coefficientPower_succ, pow_succ]
      exact (coefficientComposition_base_norm_le admissible coefficient
        (coefficientPower admissible coefficient power)).trans
          (by simpa only [mul_comm] using
            mul_le_mul_of_nonneg_left inductionHypothesis (norm_nonneg coefficient))

theorem coefficientPower_norm_le_theta {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (positive : 0 < dimension)
    (coefficient : BaseCoefficient L sigma gamma ell dimension) (theta : ℝ)
    (normBound : ‖coefficient‖ ≤ theta) (power : ℕ) :
    ‖coefficientPower admissible coefficient power‖ ≤ theta ^ power := by
  calc
    ‖coefficientPower admissible coefficient power‖ ≤ ‖coefficient‖ ^ power :=
      coefficientPower_norm_le admissible positive coefficient power
    _ ≤ theta ^ power := by gcongr

theorem coefficientPower_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (positive : 0 < dimension)
    (coefficient : BaseCoefficient L sigma gamma ell dimension) (theta : ℝ)
    (normBound : ‖coefficient‖ ≤ theta) (thetaLt : theta < 1) :
    Summable (coefficientPower admissible coefficient) := by
  have thetaNonnegative : 0 ≤ theta := (norm_nonneg coefficient).trans normBound
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le
    (fun power => norm_nonneg (coefficientPower admissible coefficient power))
    (coefficientPower_norm_le_theta admissible positive coefficient theta normBound)
    (summable_geometric_of_lt_one thetaNonnegative thetaLt)

def coefficientNeumannInverse {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (coefficient : BaseCoefficient L sigma gamma ell dimension) :
    BaseCoefficient L sigma gamma ell dimension :=
  ∑' power : ℕ, coefficientPower admissible coefficient power

theorem coefficientNeumannInverse_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (positive : 0 < dimension)
    (coefficient : BaseCoefficient L sigma gamma ell dimension) (theta : ℝ)
    (normBound : ‖coefficient‖ ≤ theta) (thetaLt : theta < 1) :
    ‖coefficientNeumannInverse admissible coefficient‖ ≤ (1 - theta)⁻¹ := by
  have thetaNonnegative : 0 ≤ theta := (norm_nonneg coefficient).trans normBound
  have scalarSummable := summable_geometric_of_lt_one thetaNonnegative thetaLt
  have normSummable : Summable (fun power : ℕ =>
      ‖coefficientPower admissible coefficient power‖) :=
    Summable.of_nonneg_of_le
      (fun power => norm_nonneg (coefficientPower admissible coefficient power))
      (coefficientPower_norm_le_theta admissible positive coefficient theta normBound)
      scalarSummable
  calc
    ‖coefficientNeumannInverse admissible coefficient‖ ≤
        ∑' power : ℕ, ‖coefficientPower admissible coefficient power‖ := by
      exact norm_tsum_le_tsum_norm normSummable
    _ ≤ ∑' power : ℕ, theta ^ power :=
      normSummable.tsum_le_tsum
        (coefficientPower_norm_le_theta admissible positive coefficient theta normBound)
        scalarSummable
    _ = (1 - theta)⁻¹ := tsum_geometric_of_lt_one thetaNonnegative thetaLt

end Grad.GaugeCoefficients.Neumann
