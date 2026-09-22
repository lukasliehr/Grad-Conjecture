import ANB8NativeScalarMultiplication

noncomputable section
set_option maxHeartbeats 1400000
open scoped ContDiff BigOperators
namespace Grad.BoundedScalarInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.NonlinearProduct Grad.GaugeCoefficients.Physical.Compensated Grad.AnalyticWeights.Calculus

def flatWeightedJet (sigma : ℝ) (cell : ℤ) (field : ClosedJet 1) : ClosedJet 1 :=
  ((Real.exp (sigma * Grad.CellWeights.cellWeight cell) : ℝ) : ℂ) • field

theorem originalWeightedJet_normalized (sigma gamma scale : ℝ) (cell : ℤ) (field : ClosedJet 1) :
    apWeightedJet sigma gamma scale cell field = smoothScalarWeightedJet (normalizedBandWeight gamma scale cell)
      (normalizedBandWeight_smooth gamma scale cell) (flatWeightedJet sigma cell field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change physicalWeight sigma gamma scale cell point.val • field.value point =
    normalizedBandWeight gamma scale cell point.val • (((Real.exp (sigma * Grad.CellWeights.cellWeight cell) : ℝ) : ℂ) • field.value point)
  rw [originalWeight_normalized, mul_smul, smul_comm]
  rfl

theorem flatWeightedJet_inverse (sigma gamma scale : ℝ) (cell : ℤ) (field : ClosedJet 1) :
    flatWeightedJet sigma cell field = smoothScalarWeightedJet (inverseBandWeight gamma scale cell)
      (inverseBandWeight_smooth gamma scale cell) (apWeightedJet sigma gamma scale cell field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change ((Real.exp (sigma * Grad.CellWeights.cellWeight cell) : ℝ) : ℂ) • field.value point =
    inverseBandWeight gamma scale cell point.val • (physicalWeight sigma gamma scale cell point.val • field.value point)
  have scalar : inverseBandWeight gamma scale cell point.val * physicalWeight sigma gamma scale cell point.val =
      Real.exp (sigma * Grad.CellWeights.cellWeight cell) := by
    rw [originalWeight_normalized]
    calc
      _ = Real.exp (sigma * Grad.CellWeights.cellWeight cell) *
          (normalizedBandWeight gamma scale cell point.val * inverseBandWeight gamma scale cell point.val) := by ring
      _ = _ := by rw [normalizedBandWeight_inverse, mul_one]
  rw [← mul_smul, scalar]
  rfl

theorem original_weighted_native_square (sigma gamma scale : ℝ) (cell : ℤ) (grade : ℕ) (field : ClosedJet 1) :
    ‖unitDiskCoreInto grade (apWeightedJet sigma gamma scale cell field)‖ ^ 2 =
      ∑ index : DerivativeIndex grade, ‖closedDerivativeL2 (derivativeMultiIndex index) (apWeightedJet sigma gamma scale cell field)‖ ^ 2 :=
  (unitDiskSobolev_norm_sq grade (unitDiskCoreInto grade (apWeightedJet sigma gamma scale cell field))).trans
    (Finset.sum_congr rfl (fun index _ => congrArg (fun value : DiskL2 1 => ‖value‖ ^ 2)
      (unitDiskDerivative_core grade index (apWeightedJet sigma gamma scale cell field))))

theorem original_weighted_native_le_row (length sigma gamma scale : ℝ) (cell : ℤ) (grade : ℕ) (field : ClosedJet 1) :
    ‖unitDiskCoreInto grade (apWeightedJet sigma gamma scale cell field)‖ ≤
      ‖apRowLinear (grade := grade) length sigma gamma scale cell field‖ := by
  have sums := Finset.sum_le_sum (s := Finset.univ) (fun (index : DerivativeIndex grade) _ =>
    le_mul_of_one_le_left (sq_nonneg ‖closedDerivativeL2 (derivativeMultiIndex index) (apWeightedJet sigma gamma scale cell field)‖)
      (one_le_pow₀ (n := 2 * (grade - derivativeOrder index)) (scaledCellWeight_one_le length scale cell)))
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    ((original_weighted_native_square sigma gamma scale cell grade field).le.trans
      (sums.trans (apRowLinear_norm_sq (grade := grade) length sigma gamma scale cell field).symm.le))

theorem original_row_le_weighted_native (length sigma gamma scale ceiling : ℝ) (cell : ℤ)
    (band : InCellBand length scale ceiling cell) (grade : ℕ) (field : ClosedJet 1) :
    ‖apRowLinear (grade := grade) length sigma gamma scale cell field‖ ≤
      bandFrequencySize ceiling ^ grade * ‖unitDiskCoreInto grade (apWeightedJet sigma gamma scale cell field)‖ := by
  have powerBound (index : DerivativeIndex grade) : scaledCellWeight length scale cell ^ (2 * (grade - derivativeOrder index)) ≤
      (bandFrequencySize ceiling ^ grade) ^ 2 := by
    calc
      _ ≤ bandFrequencySize ceiling ^ (2 * (grade - derivativeOrder index)) :=
        pow_le_pow_left₀ (scaledCellWeight_nonnegative length scale cell) (band_scaled_frequency length scale ceiling cell band) _
      _ ≤ bandFrequencySize ceiling ^ (grade * 2) := pow_le_pow_right₀ (bandFrequencySize_one_le ceiling) (by omega)
      _ = _ := pow_mul _ _ _
  have sums := Finset.sum_le_sum (s := Finset.univ) (fun (index : DerivativeIndex grade) _ =>
    mul_le_mul_of_nonneg_right (powerBound index)
      (sq_nonneg ‖closedDerivativeL2 (derivativeMultiIndex index) (apWeightedJet sigma gamma scale cell field)‖))
  have factored := (Finset.mul_sum Finset.univ
    (fun index : DerivativeIndex grade => ‖closedDerivativeL2 (derivativeMultiIndex index) (apWeightedJet sigma gamma scale cell field)‖ ^ 2)
    ((bandFrequencySize ceiling ^ grade) ^ 2)).symm
  have bound := (apRowLinear_norm_sq (grade := grade) length sigma gamma scale cell field).le.trans
    (sums.trans_eq (factored.trans (congrArg (fun value : ℝ => (bandFrequencySize ceiling ^ grade) ^ 2 * value)
      (original_weighted_native_square sigma gamma scale cell grade field).symm)))
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _))).mp
    (bound.trans_eq (mul_pow _ _ 2).symm)

def originalBandRowConstant (length gamma ceiling : ℝ) (grade : ℕ) : ℝ :=
  bandFrequencySize ceiling ^ grade * bandMultiplicationConstant length gamma ceiling grade

theorem originalBandRowConstant_nonnegative (length gamma ceiling : ℝ) (nonnegative : 0 ≤ gamma) (grade : ℕ) :
    0 ≤ originalBandRowConstant length gamma ceiling grade :=
  mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (bandMultiplicationConstant_nonnegative length gamma ceiling nonnegative grade)

/-- Uniform band comparison with the SAME sigma, at the exact original AP row. -/
theorem originalBandRow_le_flat {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (ceiling : ℝ) (cell : ℤ) (band : InCellBand length scale ceiling cell) (grade : ℕ) (field : ClosedJet 1) :
    ‖apRowLinear (grade := grade) length sigma gamma scale cell field‖ ≤
      originalBandRowConstant length gamma ceiling grade * ‖unitDiskCoreInto grade (flatWeightedJet sigma cell field)‖ := by
  have first := original_row_le_weighted_native length sigma gamma scale ceiling cell band grade field
  have second := normalizedBandWeight_native admissible ceiling cell band grade (flatWeightedJet sigma cell field)
  rw [← originalWeightedJet_normalized sigma gamma scale cell field] at second
  exact first.trans ((mul_le_mul_of_nonneg_left second (pow_nonneg (Real.sqrt_nonneg _) _)).trans_eq (mul_assoc _ _ _).symm)

theorem flat_le_originalBandRow {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (ceiling : ℝ) (cell : ℤ) (band : InCellBand length scale ceiling cell) (grade : ℕ) (field : ClosedJet 1) :
    ‖unitDiskCoreInto grade (flatWeightedJet sigma cell field)‖ ≤
      bandMultiplicationConstant length gamma ceiling grade * ‖apRowLinear (grade := grade) length sigma gamma scale cell field‖ := by
  have first := inverseBandWeight_native admissible ceiling cell band grade (apWeightedJet sigma gamma scale cell field)
  rw [← flatWeightedJet_inverse sigma gamma scale cell field] at first
  exact first.trans (mul_le_mul_of_nonneg_left (original_weighted_native_le_row length sigma gamma scale cell grade field)
    (bandMultiplicationConstant_nonnegative length gamma ceiling (admissible_gamma_nonnegative admissible) grade))

end Grad.BoundedScalarInverse
