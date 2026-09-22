import AFZ7CompletedPhysicalRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.AnalyticWeights.Higher Grad.AnalyticWeights.Calculus
open Grad.GaugeCoefficients.Neumann.Regularity

theorem apScaled_allocation_additive_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (rank : ℕ) (input shift : ℤ) :
    ell ^ rank * allocationPolynomial rank (input + shift) input ≤
      (rank + 1 : ℝ) * (max 1 L) ^ rank *
        (scaledCellWeight L ell shift + scaledCellWeight L ell input) ^ rank := by
  have ellNonnegative := admissible_ell_nonnegative admissible
  have inputNonnegative := scaledCellWeight_nonnegative L ell input
  have shiftNonnegative := scaledCellWeight_nonnegative L ell shift
  have inputFrequencyNonnegative := (Grad.CellWeights.cellWeight_pos input).le
  have shiftFrequencyNonnegative := (Grad.CellWeights.cellWeight_pos shift).le
  have maximumNonnegative : 0 ≤ max 1 L := zero_le_one.trans (le_max_left _ _)
  have singleBound (split : ℕ) (membership : split ∈ Finset.Icc 1 rank) :
      ell ^ rank * (Grad.CellWeights.cellWeight shift ^ split *
        Grad.CellWeights.cellWeight input ^ (rank - split)) ≤
      (max 1 L) ^ rank * (scaledCellWeight L ell shift + scaledCellWeight L ell input) ^ rank := by
    have splitBound := (Finset.mem_Icc.mp membership).2
    have splitIdentity : split + (rank - split) = rank := Nat.add_sub_of_le splitBound
    have ellPower : ell ^ rank = ell ^ split * ell ^ (rank - split) := by rw [← pow_add, splitIdentity]
    have maxPower : (max 1 L) ^ rank = (max 1 L) ^ split * (max 1 L) ^ (rank - split) := by
      rw [← pow_add, splitIdentity]
    calc
      _ = (ell * Grad.CellWeights.cellWeight shift) ^ split *
          (ell * Grad.CellWeights.cellWeight input) ^ (rank - split) := by
        simp only [mul_pow]
        rw [ellPower]
        ring
      _ ≤ (max 1 L * scaledCellWeight L ell shift) ^ split *
          (max 1 L * scaledCellWeight L ell input) ^ (rank - split) :=
        mul_le_mul
          (pow_le_pow_left₀ (by positivity) (originalWidth_le_scaled L ell shift admissible.1
            ellNonnegative (admissible_ell_le_one admissible)) split)
          (pow_le_pow_left₀ (by positivity) (originalWidth_le_scaled L ell input admissible.1
            ellNonnegative (admissible_ell_le_one admissible)) (rank - split))
          (by positivity) (by positivity)
      _ = (max 1 L) ^ rank *
          (scaledCellWeight L ell shift ^ split * scaledCellWeight L ell input ^ (rank - split)) := by
        simp only [mul_pow]
        rw [maxPower]
        ring
      _ ≤ (max 1 L) ^ rank *
          ((scaledCellWeight L ell shift + scaledCellWeight L ell input) ^ split *
            (scaledCellWeight L ell shift + scaledCellWeight L ell input) ^ (rank - split)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg maximumNonnegative _)
        exact mul_le_mul
          (pow_le_pow_left₀ shiftNonnegative (le_add_of_nonneg_right inputNonnegative) split)
          (pow_le_pow_left₀ inputNonnegative (le_add_of_nonneg_left shiftNonnegative) (rank - split))
          (pow_nonneg inputNonnegative _) (pow_nonneg (add_nonneg shiftNonnegative inputNonnegative) _)
      _ = (max 1 L) ^ rank * (scaledCellWeight L ell shift + scaledCellWeight L ell input) ^ rank := by
        rw [← pow_add, splitIdentity]
      _ = _ := by ring
  unfold allocationPolynomial
  simp only [add_sub_cancel_left]
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ _split ∈ Finset.Icc 1 rank,
        (max 1 L) ^ rank * (scaledCellWeight L ell shift + scaledCellWeight L ell input) ^ rank :=
      Finset.sum_le_sum singleBound
    _ = (rank : ℝ) * ((max 1 L) ^ rank * (scaledCellWeight L ell shift + scaledCellWeight L ell input) ^ rank) := by simp
    _ ≤ (rank + 1 : ℝ) * ((max 1 L) ^ rank * (scaledCellWeight L ell shift + scaledCellWeight L ell input) ^ rank) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring


theorem apRatio_derivative_additive_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (rank : ℕ) (input shift : ℤ) (point : ClosedDisk) :
    ‖iteratedFDeriv ℝ rank (weightRatio sigma gamma ell (input + shift) input) point.val‖ ≤
      apRatioConstant L sigma gamma rank * (scaledCellWeight L ell shift + scaledCellWeight L ell input) ^ rank * originalEnvelope sigma gamma ell shift point.val := by
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
  have scaledBound := apScaled_allocation_additive_bound admissible rank input shift
  have costAllocation : weightCost rank gamma ell * allocationPolynomial rank (input + shift) input ≤
      (1 + gamma) ^ rank * ((rank + 1 : ℝ) * (max 1 L) ^ rank *
        (scaledCellWeight L ell shift + scaledCellWeight L ell input) ^ rank) := by
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
          (scaledCellWeight L ell shift + scaledCellWeight L ell input) ^ rank)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left ratioBound constantNonnegative) costAllocation
        (by unfold weightCost; split <;> positivity) (by unfold phaseConstant; positivity)
    _ = _ := by rw [apRatioConstant, if_neg zeroRank]; ring


theorem apRatioDerivative_additive_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (rank : ℕ) (word : Fin rank → Fin 2)
    (input shift : ℤ) (point : ClosedDisk) :
    |apRatioDerivative sigma gamma ell rank word input shift point| ≤
      apRatioConstant L sigma gamma rank *
        (scaledCellWeight L ell shift + scaledCellWeight L ell input) ^ rank *
          originalEnvelope sigma gamma ell shift point.val :=
  (orderedDerivative_norm_le rank word _ point.val).trans
    (apRatio_derivative_additive_bound admissible rank input shift point)

end Grad.GaugeCoefficients.Physical.RadialLedger
