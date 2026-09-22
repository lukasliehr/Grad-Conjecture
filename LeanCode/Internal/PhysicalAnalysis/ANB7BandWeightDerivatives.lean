import ANB6NormalizedBandWeight

noncomputable section
set_option maxHeartbeats 1400000
open scoped ContDiff
namespace Grad.BoundedScalarInverse
open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.AnalyticWeights.Calculus Grad.AnalyticWeights.Higher

def bandWeightDerivativeConstant (length gamma ceiling : ℝ) (order : ℕ) : ℝ :=
  if order = 0 then bandWeightCeiling length gamma ceiling else
    partitionProductConstant order * gamma * (1 + gamma) ^ (order - 1) *
      bandPhaseSize length ceiling ^ order * bandWeightCeiling length gamma ceiling

theorem bandWeightDerivativeConstant_nonnegative (length gamma ceiling : ℝ) (nonnegative : 0 ≤ gamma) (order : ℕ) :
    0 ≤ bandWeightDerivativeConstant length gamma ceiling order := by
  have partition := partitionProductConstant_nonnegative order
  have phaseSize := bandPhaseSize_nonnegative length ceiling
  have positive := Real.exp_pos (gamma * bandPhaseSize length ceiling)
  unfold bandWeightDerivativeConstant bandWeightCeiling
  split <;> positivity

private theorem absorb_band_derivative (order : ℕ) (value coefficient scale weight frequency size ceiling : ℝ)
    (coefficientNonnegative : 0 ≤ coefficient) (scaleNonnegative : 0 ≤ scale)
    (frequencyNonnegative : 0 ≤ frequency) (weightNonnegative : 0 ≤ weight)
    (frequencyBound : scale * frequency ≤ size) (weightBound : weight ≤ ceiling)
    (bound : value ≤ coefficient * scale ^ order * weight * frequency ^ order) :
    value ≤ coefficient * size ^ order * ceiling := by
  have rearranged : value ≤ coefficient * (scale * frequency) ^ order * weight :=
    bound.trans_eq (by rw [mul_pow]; ring)
  exact rearranged.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg scaleNonnegative frequencyNonnegative) frequencyBound order)
      coefficientNonnegative) weightBound weightNonnegative
      (mul_nonneg coefficientNonnegative (pow_nonneg ((mul_nonneg scaleNonnegative frequencyNonnegative).trans frequencyBound) _)))

theorem normalizedBandWeight_derivative_bound {length sigma gamma scale : ℝ}
    (admissible : Admissible length sigma gamma scale) (ceiling : ℝ) (cell : ℤ)
    (band : InCellBand length scale ceiling cell) (order : ℕ) (point : ClosedDisk) :
    ‖iteratedFDeriv ℝ order (normalizedBandWeight gamma scale cell) point.val‖ ≤
      bandWeightDerivativeConstant length gamma ceiling order := by
  by_cases zero : order = 0
  · subst order
    rw [norm_iteratedFDeriv_zero, Real.norm_of_nonneg
      (show 0 ≤ normalizedBandWeight gamma scale cell point.val from (Real.exp_pos _).le)]
    exact normalizedBandWeight_le admissible ceiling cell point.val
  have bound := physicalWeight_iterated_norm_bound 0 gamma scale cell
    (admissible_gamma_nonnegative admissible) (admissible_ell_nonnegative admissible) order (by omega) point.val
  rw [weightCost, if_neg zero] at bound
  have adjusted : ‖iteratedFDeriv ℝ order (normalizedBandWeight gamma scale cell) point.val‖ ≤
      (partitionProductConstant order * gamma * (1 + gamma) ^ (order - 1)) * scale ^ order *
        normalizedBandWeight gamma scale cell point.val * Grad.CellWeights.cellWeight cell ^ order := bound.trans_eq (by unfold normalizedBandWeight; ring)
  have estimate := absorb_band_derivative order _ _ _ _ _ _ _
    (mul_nonneg (mul_nonneg (partitionProductConstant_nonnegative order) (admissible_gamma_nonnegative admissible))
      (pow_nonneg (by linarith [admissible_gamma_nonnegative admissible]) _))
    (admissible_ell_nonnegative admissible) (Grad.CellWeights.cellWeight_pos cell).le (Real.exp_pos _).le
    (band_original_frequency admissible ceiling cell band) (normalizedBandWeight_le admissible ceiling cell point.val) adjusted
  exact estimate.trans_eq (by rw [bandWeightDerivativeConstant, if_neg zero])

theorem inverseBandWeight_derivative_bound {length sigma gamma scale : ℝ}
    (admissible : Admissible length sigma gamma scale) (ceiling : ℝ) (cell : ℤ)
    (band : InCellBand length scale ceiling cell) (order : ℕ) (point : ClosedDisk) :
    ‖iteratedFDeriv ℝ order (inverseBandWeight gamma scale cell) point.val‖ ≤
      bandWeightDerivativeConstant length gamma ceiling order := by
  by_cases zero : order = 0
  · subst order
    rw [norm_iteratedFDeriv_zero, Real.norm_of_nonneg (by
      rw [inverseBandWeight, inverseWeight_exp]; exact (Real.exp_pos _).le)]
    exact inverseBandWeight_le admissible ceiling cell band point
  have bound := inverseWeight_iterated_norm_bound 0 gamma scale cell
    (admissible_gamma_nonnegative admissible) (admissible_ell_nonnegative admissible) order (by omega) point.val
  rw [weightCost, if_neg zero] at bound
  have adjusted : ‖iteratedFDeriv ℝ order (inverseBandWeight gamma scale cell) point.val‖ ≤
      (partitionProductConstant order * gamma * (1 + gamma) ^ (order - 1)) * scale ^ order *
        inverseBandWeight gamma scale cell point.val * Grad.CellWeights.cellWeight cell ^ order := bound.trans_eq (by unfold inverseBandWeight; ring)
  have estimate := absorb_band_derivative order _ _ _ _ _ _ _
    (mul_nonneg (mul_nonneg (partitionProductConstant_nonnegative order) (admissible_gamma_nonnegative admissible))
      (pow_nonneg (by linarith [admissible_gamma_nonnegative admissible]) _))
    (admissible_ell_nonnegative admissible) (Grad.CellWeights.cellWeight_pos cell).le
    (show 0 ≤ inverseBandWeight gamma scale cell point.val by rw [inverseBandWeight, inverseWeight_exp]; exact (Real.exp_pos _).le)
    (band_original_frequency admissible ceiling cell band) (inverseBandWeight_le admissible ceiling cell band point) adjusted
  exact estimate.trans_eq (by rw [bandWeightDerivativeConstant, if_neg zero])

end Grad.BoundedScalarInverse
