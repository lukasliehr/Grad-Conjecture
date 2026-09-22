import GC17Interface

noncomputable section

set_option maxHeartbeats 1200000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.InverseAllocation

theorem identityFamily_coherent (L sigma gamma ell : ℝ) (dimension : ℕ) :
    FamilyCoherent (fun grade => gradedIdentityCoefficient L sigma gamma ell grade dimension) := by
  intro grade other index otherIndex same cell point
  have sameOrder : derivativeOrder index = derivativeOrder otherIndex := congrArg cartesianOrder same
  by_cases orderZero : derivativeOrder index = 0
  · have otherZero : derivativeOrder otherIndex = 0 := sameOrder ▸ orderZero
    rw [derivativeIndex_eq_zeroDerivativeIndexAt_of_order_zero index orderZero,
      derivativeIndex_eq_zeroDerivativeIndexAt_of_order_zero otherIndex otherZero,
      gradedIdentityCoefficient_zeroDerivative, gradedIdentityCoefficient_zeroDerivative]
  · rw [gradedIdentityCoefficient_positiveDerivative L sigma gamma ell grade dimension cell index
      (Nat.pos_of_ne_zero orderZero) point,
      gradedIdentityCoefficient_positiveDerivative L sigma gamma ell other dimension cell otherIndex
        (by omega) point]

theorem powerFamily_coherent {L sigma gamma ell : ℝ} {dimension : ℕ}
    (admissible : Admissible L sigma gamma ell)
    (family : CoefficientFamily L sigma gamma ell dimension dimension)
    (coherent : FamilyCoherent family) (power : ℕ) :
    FamilyCoherent (fun grade => gradedCoefficientPower admissible (family grade) power) := by
  induction power with
  | zero => exact identityFamily_coherent L sigma gamma ell dimension
  | succ power ih => exact coherent.comp admissible ih

/-- All spatial orders of the actual GC12 inverse are coherent because
the same ordered powers are summable at every grade on the same base ball. -/
theorem inverseFamily_coherent {L sigma gamma ell : ℝ} {dimension : ℕ}
    (admissible : Admissible L sigma gamma ell) (positive : 0 < dimension)
    (family : CoefficientFamily L sigma gamma ell dimension dimension)
    (coherent : FamilyCoherent family) (theta : ℝ)
    (baseBound : ‖family 0‖ ≤ theta) (thetaLt : theta < 1) :
    FamilyCoherent (inverseFamily admissible family) := by
  have powersSummable (grade : ℕ) : Summable (gradedCoefficientPower admissible (family grade)) :=
    gradedCoefficientPower_summable admissible positive (family 0) (family grade) theta
      (coherent_realizes family coherent grade) baseBound thetaLt
  intro grade other index otherIndex same cell point
  change coefficientDerivative (∑' power : ℕ, gradedCoefficientPower admissible (family grade) power)
      cell index point =
    coefficientDerivative (∑' power : ℕ, gradedCoefficientPower admissible (family other) power)
      cell otherIndex point
  rw [seedDerivative_tsum _ (powersSummable grade), seedDerivative_tsum _ (powersSummable other)]
  apply tsum_congr
  intro power
  exact powerFamily_coherent admissible family coherent power grade other index otherIndex same cell point

theorem coherent_physicalValue {L sigma gamma ell : ℝ} {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (family grade) angle point = fourierEvaluation (family 0) angle point := by
  apply tsum_congr
  intro cell
  exact congrArg (fun value : OperatorValue input output => fourierPhase cell angle • value)
    (coherent grade 0 (zeroDerivativeIndexAt grade) zeroDerivativeIndex rfl cell point)

theorem inverseFamily_physicalValue {L sigma gamma ell : ℝ} {dimension : ℕ}
    (admissible : Admissible L sigma gamma ell) (positive : 0 < dimension)
    (family : CoefficientFamily L sigma gamma ell dimension dimension)
    (coherent : FamilyCoherent family) (theta : ℝ)
    (baseBound : ‖family 0‖ ≤ theta) (thetaLt : theta < 1)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (inverseFamily admissible family grade) angle point =
      fourierEvaluation (analyticCapCoefficientNeumannInverse admissible (family 0)) angle point := by
  have realizes := gradedCoefficientNeumannInverse_realizes admissible positive
    (family 0) (family grade) theta (coherent_realizes family coherent grade) baseBound thetaLt
  apply tsum_congr
  intro cell
  exact congrArg (fun value : OperatorValue dimension dimension => fourierPhase cell angle • value)
    (realizes cell point)

end Grad.GaugeCoefficients.Physical.Ledger
