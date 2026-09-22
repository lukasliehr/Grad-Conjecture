import GC12Base

noncomputable section

set_option maxHeartbeats 3000000

open Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann.Regularity

open Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Neumann

noncomputable instance gradedCoefficientCompleteSpace
    (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ) :
    CompleteSpace (Coefficient L sigma gamma ell grade inputDimension outputDimension) :=
  completeSpace_of_isComplete_univ
    (coefficient_complete grade inputDimension outputDimension)

/-- Powers formed in the original grade, using the same written composition
order as the frozen base Neumann series. -/
def gradedCoefficientPower {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (power : ℕ) : Coefficient L sigma gamma ell grade dimension dimension :=
  Nat.rec (gradedIdentityCoefficient L sigma gamma ell grade dimension)
    (fun _ previous => coefficientComposition admissible grade coefficient previous) power

@[simp] theorem gradedCoefficientPower_zero {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade dimension dimension) :
    gradedCoefficientPower admissible coefficient 0 =
      gradedIdentityCoefficient L sigma gamma ell grade dimension := rfl

@[simp] theorem gradedCoefficientPower_succ {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (power : ℕ) :
    gradedCoefficientPower admissible coefficient (power + 1) =
      coefficientComposition admissible grade coefficient
        (gradedCoefficientPower admissible coefficient power) := rfl

theorem gradedCoefficientPower_realizes {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (baseCoefficient : BaseCoefficient L sigma gamma ell dimension)
    (gradedCoefficient : Coefficient L sigma gamma ell grade dimension dimension)
    (realizes : RealizesSameCoefficient baseCoefficient gradedCoefficient) :
    ∀ power : ℕ, RealizesSameCoefficient
      (coefficientPower admissible baseCoefficient power)
      (gradedCoefficientPower admissible gradedCoefficient power) := by
  intro power
  induction power with
  | zero =>
      simpa only [coefficientPower_zero, gradedCoefficientPower_zero] using
        gradedIdentity_realizes L sigma gamma ell grade dimension
  | succ power inductionHypothesis =>
      simpa only [coefficientPower_succ, gradedCoefficientPower_succ] using
        realizesSameCoefficient_composition admissible realizes inductionHypothesis

def gradedCoefficientNeumannInverse {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade dimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade dimension dimension) :
    Coefficient L sigma gamma ell grade dimension dimension :=
  ∑' power : ℕ, gradedCoefficientPower admissible coefficient power

end Grad.GaugeCoefficients.Neumann.Regularity
