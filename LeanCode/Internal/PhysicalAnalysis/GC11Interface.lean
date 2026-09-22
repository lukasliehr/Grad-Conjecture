import GC10Proof

noncomputable section

open Grad.GenericCarriers Grad.ClosedJets Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann

open Grad.GaugeCoefficients.Algebra

abbrev BaseCoefficient (L sigma gamma ell : ℝ) (dimension : ℕ) :=
  Coefficient L sigma gamma ell 0 dimension dimension

/-- Powers in the completed base coefficient algebra, with multiplication in
the written operator-composition order. -/
def coefficientPower {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (coefficient : BaseCoefficient L sigma gamma ell dimension) (power : ℕ) :
    BaseCoefficient L sigma gamma ell dimension :=
  Nat.rec (identityCoefficient L sigma gamma ell dimension)
    (fun _ previous => coefficientComposition admissible 0 coefficient previous) power

/-- The exact base Neumann inverse package from AP12. -/
structure InverseWitness {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (coefficient : BaseCoefficient L sigma gamma ell dimension) (theta : ℝ) where
  inverse : BaseCoefficient L sigma gamma ell dimension
  powers_summable : Summable (coefficientPower admissible coefficient)
  series : inverse = ∑' power : ℕ, coefficientPower admissible coefficient power
  left_inverse :
    coefficientComposition admissible 0
        (identityCoefficient L sigma gamma ell dimension - coefficient) inverse =
      identityCoefficient L sigma gamma ell dimension
  right_inverse :
    coefficientComposition admissible 0 inverse
        (identityCoefficient L sigma gamma ell dimension - coefficient) =
      identityCoefficient L sigma gamma ell dimension
  base_norm : ‖inverse‖ ≤ (1 - theta)⁻¹
  pointwise_inverse : ∀ (angle : ℝ) (point : ClosedDisk),
    (ContinuousLinearMap.id ℂ (PhysicalValue dimension) -
        fourierEvaluation coefficient angle point).comp
          (fourierEvaluation inverse angle point) =
        ContinuousLinearMap.id ℂ (PhysicalValue dimension) ∧
      (fourierEvaluation inverse angle point).comp
          (ContinuousLinearMap.id ℂ (PhysicalValue dimension) -
            fourierEvaluation coefficient angle point) =
        ContinuousLinearMap.id ℂ (PhysicalValue dimension)

def BlockGoal : Prop :=
  ∀ (L sigma gamma ell : ℝ) (admissible : Admissible L sigma gamma ell)
    (dimension : ℕ), 0 < dimension →
    ∀ (coefficient : BaseCoefficient L sigma gamma ell dimension) (theta : ℝ),
      ‖coefficient‖ ≤ theta → theta < 1 →
        Nonempty (InverseWitness admissible coefficient theta)

end Grad.GaugeCoefficients.Neumann
