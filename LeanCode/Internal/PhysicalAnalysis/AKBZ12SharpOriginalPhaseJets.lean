import AKBZ11SharpScaledPhaseAllocation

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.AnalyticWeights.Higher Grad.AnalyticWeights.Calculus
open Grad.GaugeCoefficients.Physical.RadialLedger

def sharpPhaseConstant (L sigma gamma : ℝ) (rank : ℕ) : ℝ :=
  commonConstant rank*(1+gamma)^rank*(max 1 L)^rank*phaseConstant sigma gamma

theorem sharpPhaseConstant_nonnegative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (rank : ℕ) :
    0≤sharpPhaseConstant L sigma gamma rank := by
  have gammaNonnegative := admissible_gamma_nonnegative admissible
  have common := (commonConstant_pos rank).le
  unfold sharpPhaseConstant phaseConstant
  positivity

/-- Actual original phase derivatives with the displacement sum retained.
No input reserve or coefficient order is replaced by a coarser rank. -/
theorem sharpOriginalPhase_derivative_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (rank : ℕ) (rankPositive : 0<rank)
    (input shift : ℤ) (point : ClosedDisk) :
    ‖iteratedFDeriv ℝ rank (weightRatio sigma gamma ell (input+shift) input) point.val‖ ≤
      sharpPhaseConstant L sigma gamma rank*originalEnvelope sigma gamma ell shift point.val*
        ∑ displacement ∈ Finset.Icc 1 rank,
          scaledCellWeight L ell shift^displacement*scaledCellWeight L ell input^(rank-displacement) := by
  have gammaNonnegative := admissible_gamma_nonnegative admissible
  have gammaLeOne : gamma≤1 := ((lt_min_iff.mp admissible.2.2.1).1).le
  have inputNonnegative := scaledCellWeight_nonnegative L ell input
  have shiftNonnegative := scaledCellWeight_nonnegative L ell shift
  have ellNonnegative := admissible_ell_nonnegative admissible
  have common := (commonConstant_pos rank).le
  have envelopePositive : 0<originalEnvelope sigma gamma ell shift point.val := Real.exp_pos _
  have ratioPositive := (ratioGoal sigma gamma ell (input+shift) input point.val).1
  have ratioBound := apRatio_envelope admissible input shift point
  have gammaPower : gamma*(1+gamma)^(rank-1)≤(1+gamma)^rank := by
    calc
      _ ≤ 1*(1+gamma)^(rank-1) := mul_le_mul_of_nonneg_right gammaLeOne (by positivity)
      _ ≤ _ := by rw [one_mul]; exact pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _)
  have allocationNonnegative : 0≤allocationPolynomial rank (input+shift) input := by
    unfold allocationPolynomial
    exact Finset.sum_nonneg fun _ _ => mul_nonneg
      (pow_nonneg (Grad.CellWeights.cellWeight_pos _).le _) (pow_nonneg (Grad.CellWeights.cellWeight_pos _).le _)
  have maximumNonnegative : 0≤max 1 L := zero_le_one.trans (le_max_left _ _)
  have scaled := sharpScaled_phase_allocation admissible rank input shift
  have cost : weightCost rank gamma ell*allocationPolynomial rank (input+shift) input ≤
      (1+gamma)^rank*((max 1 L)^rank*∑ displacement ∈ Finset.Icc 1 rank,
        scaledCellWeight L ell shift^displacement*scaledCellWeight L ell input^(rank-displacement)) := by
    rw [weightCost, if_neg (by omega)]
    calc
      _ = (gamma*(1+gamma)^(rank-1))*(ell^rank*allocationPolynomial rank (input+shift) input) := by ring
      _ ≤ _ := mul_le_mul gammaPower scaled (by positivity) (by positivity)
  have derivative := (exponentialGoal sigma gamma ell gammaNonnegative ellNonnegative rank rankPositive
    (input+shift) input point.val).1
  calc
    _ ≤ commonConstant rank*weightRatio sigma gamma ell (input+shift) input point.val*
      (weightCost rank gamma ell*allocationPolynomial rank (input+shift) input) := by
        convert derivative using 1
        ring
    _ ≤ commonConstant rank*(phaseConstant sigma gamma*originalEnvelope sigma gamma ell shift point.val)*
        ((1+gamma)^rank*((max 1 L)^rank*∑ displacement ∈ Finset.Icc 1 rank,
          scaledCellWeight L ell shift^displacement*scaledCellWeight L ell input^(rank-displacement))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left ratioBound common) cost
        (by unfold weightCost; split <;> positivity) (by unfold phaseConstant; positivity)
    _ = _ := by unfold sharpPhaseConstant; ring

end Grad.OriginalCartesianTameEstimate
