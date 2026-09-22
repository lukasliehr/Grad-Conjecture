import ANB11HilbertColumns

noncomputable section
namespace Grad.BoundedScalarInverse
open Grad.CircularNormalLift Grad.BoundaryTrace Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.GaugeCoefficients.Envelope

def boundaryFlatRatio (length sigma gamma scale : ℝ) (order : ℕ) (cell mode : ℤ) : ℝ :=
  Real.exp (sigma * Grad.CellWeights.cellWeight cell) * normalBoundaryWeight (order + 2) mode /
    apBoundaryWeight length sigma gamma scale (order + 1) (mode, cell)

theorem ordinaryBoundaryWeight_le (length scale : ℝ) (order : ℕ) (cell mode : ℤ) :
    normalBoundaryWeight (order + 2) mode ≤
      Real.sqrt (apBoundaryFrequency length scale (mode, cell) ^ (2 * (order + 1) - 1)) := by
  have frequency : apBoundaryFrequency 1 1 (mode, 0) ≤ apBoundaryFrequency length scale (mode, cell) := by
    apply Real.sqrt_le_sqrt
    simp only [Int.cast_zero, zero_mul, zero_div, zero_pow (by decide : 2 ≠ 0), add_zero]
    nlinarith [sq_nonneg ((cell : ℝ) * scale / length)]
  have power := pow_le_pow_left₀ (apBoundaryFrequency_pos 1 1 (mode, 0)).le frequency (2 * (order + 1) - 1)
  simpa [normalBoundaryWeight, apBoundaryWeight, apBoundaryPhase, Grad.AnalyticWeights.phase] using Real.sqrt_le_sqrt power

theorem boundaryFlatRatio_nonnegative (length sigma gamma scale : ℝ) (order : ℕ) (cell mode : ℤ) :
    0 ≤ boundaryFlatRatio length sigma gamma scale order cell mode :=
  div_nonneg (mul_nonneg (Real.exp_pos _).le (normalBoundaryWeight_pos _ _).le)
    (apBoundaryWeight_pos _ _ _ _ _ _).le

theorem boundaryFlatRatio_bound {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (ceiling : ℝ) (cell : ℤ) (band : InCellBand length scale ceiling cell) (order : ℕ) (mode : ℤ) :
    boundaryFlatRatio length sigma gamma scale order cell mode ≤ bandWeightCeiling length gamma ceiling := by
  have gammaNonnegative := admissible_gamma_nonnegative admissible
  have phaseBound := (Grad.AnalyticWeights.phase_linear_bounds sigma gamma scale cell gammaNonnegative
    (admissible_ell_nonnegative admissible)).1
  have frequency := band_original_frequency admissible ceiling cell band
  have exponent : sigma * Grad.CellWeights.cellWeight cell - apBoundaryPhase sigma gamma scale cell ≤
      gamma * bandPhaseSize length ceiling := by
    have upper := mul_le_mul_of_nonneg_left frequency gammaNonnegative
    unfold Grad.AnalyticWeights.rate at phaseBound
    change (sigma - gamma * scale) * Grad.CellWeights.cellWeight cell ≤ apBoundaryPhase sigma gamma scale cell at phaseBound
    nlinarith
  have exponential := Real.exp_le_exp.mpr exponent
  have weight := ordinaryBoundaryWeight_le length scale order cell mode
  unfold boundaryFlatRatio
  apply (div_le_iff₀ (apBoundaryWeight_pos _ _ _ _ _ _)).2
  calc
    _ ≤ Real.exp (sigma * Grad.CellWeights.cellWeight cell) *
        Real.sqrt (apBoundaryFrequency length scale (mode, cell) ^ (2 * (order + 1) - 1)) :=
      mul_le_mul_of_nonneg_left weight (Real.exp_pos _).le
    _ ≤ bandWeightCeiling length gamma ceiling * apBoundaryWeight length sigma gamma scale (order + 1) (mode, cell) := by
      have same : Real.exp (sigma * Grad.CellWeights.cellWeight cell) =
          Real.exp (sigma * Grad.CellWeights.cellWeight cell - apBoundaryPhase sigma gamma scale cell) *
            Real.exp (apBoundaryPhase sigma gamma scale cell) := by rw [← Real.exp_add]; congr 1; ring
      rw [same, apBoundaryWeight]
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right exponential (Real.exp_pos _).le)
        (Real.sqrt_nonneg _)).trans_eq (mul_assoc _ _ _)

end Grad.BoundedScalarInverse
