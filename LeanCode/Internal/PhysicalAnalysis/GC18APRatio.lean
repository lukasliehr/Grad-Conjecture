import GC18APWeights

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.AnalyticWeights.Higher Grad.AnalyticWeights.Calculus

def apRatioConstant (L sigma gamma : ℝ) (rank : ℕ) : ℝ :=
  if rank = 0 then phaseConstant sigma gamma else
    commonConstant rank * (1 + gamma) ^ rank * (rank + 1) * (max 1 L) ^ rank * phaseConstant sigma gamma

theorem apRatioConstant_nonnegative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (rank : ℕ) : 0 ≤ apRatioConstant L sigma gamma rank := by
  have gammaNonnegative := admissible_gamma_nonnegative admissible
  have constantNonnegative := (commonConstant_pos rank).le
  unfold apRatioConstant phaseConstant
  split <;> positivity

theorem apRatio_envelope {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (input shift : ℤ) (point : ClosedDisk) :
    weightRatio sigma gamma ell (input + shift) input point.val ≤
      phaseConstant sigma gamma * originalEnvelope sigma gamma ell shift point.val := by
  have bound := Grad.GaugeCoefficients.Envelope.ratioGoal L sigma gamma ell admissible input shift point.val
    (by simpa only [closedDisk, Metric.mem_closedBall, dist_zero_right] using
      (show ‖point.val‖ ≤ 1 from point.property))
  simpa only [weightRatio, originalWeight, inverseWeight, div_eq_mul_inv] using bound

theorem apRatio_derivative_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (rank : ℕ) (input shift : ℤ) (point : ClosedDisk) :
    ‖iteratedFDeriv ℝ rank (weightRatio sigma gamma ell (input + shift) input) point.val‖ ≤
      apRatioConstant L sigma gamma rank * scaledCellWeight L ell shift ^ rank *
        scaledCellWeight L ell input ^ rank * originalEnvelope sigma gamma ell shift point.val := by
  have gammaNonnegative := admissible_gamma_nonnegative admissible
  have gammaLeOne : gamma ≤ 1 := ((lt_min_iff.mp admissible.2.2.1).1).le
  have ellNonnegative := admissible_ell_nonnegative admissible
  have inputNonnegative := scaledCellWeight_nonnegative L ell input
  have shiftNonnegative := scaledCellWeight_nonnegative L ell shift
  have maximumNonnegative : 0 ≤ max 1 L := zero_le_one.trans (le_max_left _ _)
  have constantNonnegative := (commonConstant_pos rank).le
  have ratioPositive := (Grad.AnalyticWeights.Higher.ratioGoal sigma gamma ell (input + shift) input point.val).1
  have envelopePositive : 0 < originalEnvelope sigma gamma ell shift point.val := Real.exp_pos _
  have ratioBound := apRatio_envelope admissible input shift point
  by_cases zeroRank : rank = 0
  · subst rank
    simpa [norm_iteratedFDeriv_zero, Real.norm_of_nonneg ratioPositive.le, apRatioConstant] using ratioBound
  have positiveRank : 1 ≤ rank := Nat.one_le_iff_ne_zero.mpr zeroRank
  have allocationNonnegative : 0 ≤ allocationPolynomial rank (input + shift) input := by
    unfold allocationPolynomial
    exact Finset.sum_nonneg fun split _ => mul_nonneg
      (pow_nonneg (Grad.CellWeights.cellWeight_pos _).le _) (pow_nonneg (Grad.CellWeights.cellWeight_pos _).le _)
  have gammaPower : gamma * (1 + gamma) ^ (rank - 1) ≤ (1 + gamma) ^ rank := by
    calc
      _ ≤ 1 * (1 + gamma) ^ (rank - 1) := mul_le_mul_of_nonneg_right gammaLeOne (by positivity)
      _ ≤ (1 + gamma) ^ rank := by
        rw [one_mul]
        exact pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _)
  have scaledBound := apScaled_allocation_bound admissible rank input shift
  have costAllocation : weightCost rank gamma ell * allocationPolynomial rank (input + shift) input ≤
      (1 + gamma) ^ rank * ((rank + 1 : ℝ) * (max 1 L) ^ rank *
        scaledCellWeight L ell shift ^ rank * scaledCellWeight L ell input ^ rank) := by
    rw [weightCost, if_neg zeroRank]
    calc
      _ = (gamma * (1 + gamma) ^ (rank - 1)) *
          (ell ^ rank * allocationPolynomial rank (input + shift) input) := by ring
      _ ≤ _ := mul_le_mul gammaPower scaledBound (by positivity) (by positivity)
  have derivative := (exponentialGoal sigma gamma ell gammaNonnegative ellNonnegative rank positiveRank
    (input + shift) input point.val).1
  calc
    _ ≤ commonConstant rank * weightRatio sigma gamma ell (input + shift) input point.val *
        (weightCost rank gamma ell * allocationPolynomial rank (input + shift) input) := by
      convert derivative using 1
      ring
    _ ≤ commonConstant rank *
        (phaseConstant sigma gamma * originalEnvelope sigma gamma ell shift point.val) *
        ((1 + gamma) ^ rank * ((rank + 1 : ℝ) * (max 1 L) ^ rank *
          scaledCellWeight L ell shift ^ rank * scaledCellWeight L ell input ^ rank)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left ratioBound constantNonnegative) costAllocation
        (by unfold weightCost; split <;> positivity) (by unfold phaseConstant; positivity)
    _ = _ := by rw [apRatioConstant, if_neg zeroRank]; ring

end Grad.GaugeCoefficients.Physical.RadialLedger
