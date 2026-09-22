import AKN3RemainderDerivativeBounds
import SCD10FourierPaidBound

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.ExhaustionSourceAllocation

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.SourceCollarDivision
open Grad.NonlinearRadial Grad.BoundaryTrace

def paidRemainderConstant (depth order : ℕ) : ℝ :=
  remainderDerivativeConstant depth order * (6 * diskSupConstant)

theorem paidRemainderConstant_nonnegative (depth order : ℕ) : 0 ≤ paidRemainderConstant depth order :=
  mul_nonneg (remainderDerivativeConstant_nonnegative _ _)
    (mul_nonneg (by norm_num) diskSupConstant_pos.le)

/-- The original phase weight stays inside every Cartesian derivative.
The exact cost is `depth + order + power + 2`. -/
theorem polarTaylorRemainder_derivative_paid {dimension grade : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (depth order power : ℕ) (paid : depth + order + power + 2 ≤ grade)
    (point : ℝ × ℝ) (inside : point ∈ polarRectangle) :
    cellFrequency cell ^ power *
      ‖iteratedFDeriv ℝ order (polarTaylorRemainder depth (phaseWeightedJet parameters cell field)) point‖ ≤
      paidRemainderConstant depth order * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
  let frequency := cellFrequency cell ^ power
  let sourceNorm := ‖cellGradeRowLinear (grade := grade) parameters cell field‖
  have frequencyPositive : 0 < frequency := pow_pos (cellFrequency_pos cell) _
  have words (rank : ℕ) (smaller : rank ≤ order + depth) (word : CartesianWord rank) :
      ‖closedDerivative (phaseWeightedJet parameters cell field) rank word‖ ≤
        ((6 * diskSupConstant) * sourceNorm) / frequency := by
    apply (le_div_iff₀ frequencyPositive).mpr
    simpa only [mul_comm, frequency, sourceNorm] using
      weighted_word_sup_paid (power := power) parameters cell field word (by omega)
  have bound := polarTaylorRemainder_derivative_bound depth order
    (phaseWeightedJet parameters cell field) (((6 * diskSupConstant) * sourceNorm) / frequency)
    (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) diskSupConstant_pos.le) (norm_nonneg _))
      frequencyPositive.le) words point inside
  apply (mul_le_mul_of_nonneg_left bound frequencyPositive.le).trans_eq
  rw [paidRemainderConstant]
  field_simp
  ring

theorem polarTaylorRemainder_angular_paid {dimension grade : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (depth angular power : ℕ) (paid : depth + angular + power + 2 ≤ grade)
    (point : ℝ × ℝ) (inside : point ∈ polarRectangle) :
    cellFrequency cell ^ power *
      ‖angularJet angular (polarTaylorRemainder depth (phaseWeightedJet parameters cell field)) point‖ ≤
      paidRemainderConstant depth angular * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ :=
  (mul_le_mul_of_nonneg_left (angularJet_norm_le _ _ _) (pow_nonneg (cellFrequency_pos cell).le _)).trans
    (polarTaylorRemainder_derivative_paid parameters cell field depth angular power paid point inside)

theorem polarTaylorRemainder_mixed_paid {dimension grade depth radial angular power : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (paid : depth + angular + radial + power + 2 ≤ grade)
    (point : ℝ × ℝ) (inside : point ∈ polarRectangle) :
    cellFrequency cell ^ power *
      ‖angularJet angular (radialIter radial (polarTaylorRemainder depth (phaseWeightedJet parameters cell field))) point‖ ≤
      paidRemainderConstant depth (angular + radial) * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ :=
  (mul_le_mul_of_nonneg_left
    (radialAngular_norm_le radial angular _ (polarTaylorRemainder_smooth depth _) point)
    (pow_nonneg (cellFrequency_pos cell).le _)).trans
    (polarTaylorRemainder_derivative_paid parameters cell field depth (angular + radial) power (by omega) point inside)

end Grad.ExhaustionSourceAllocation
