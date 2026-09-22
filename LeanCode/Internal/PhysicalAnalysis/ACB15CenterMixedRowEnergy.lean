import ACB14ActualCenterOuterRows

noncomputable section
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators Interval
namespace Grad.ActualCenterBounds
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.ActualCenterVolterra Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.CollarCartesian Grad.ActualRadialWords Grad.BoundaryLift

theorem centerWordRow_radial_integral (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (profile : ℝ → ComplexEuclidean 1) (smooth : ContDiffOn ℝ ∞ profile (Icc (1 / 2 : ℝ) 1))
    (order : ℕ) (word : CartesianWord order) :
    (∫ time in (0 : ℝ)..(1 / 2 : ℝ), ‖centerWordRows profile order word mode time‖ ^ 2) ≤
      2 * radialWithinEnergy (1 / 2) (wordCount word 0) profile := by
  have unit : |(mode : ℝ)| = 1 := by rcases center with rfl | rfl <;> norm_num
  have continuousDensity := (smooth.continuousOn_iteratedDerivWithin
    (m := wordCount word 0) (by exact_mod_cast (le_top : (wordCount word 0 : ℕ∞) ≤ ⊤))
    (uniqueDiffOn_Icc (by norm_num : (1 / 2 : ℝ) < 1))).norm.pow 2
  have estimate := reflected_integral_le_radial _ continuousDensity (fun _ _ => sq_nonneg _)
  simp only [centerWordRows, wordAmplitude_norm_sq, unit, one_pow, one_mul]
  exact estimate

def centerMixedRowFactor (grade : ℕ) : ℝ :=
  (2 * Real.pi) * ∑ order ∈ Finset.range (grade + 1), productWordCoefficientSum order ^ 2

theorem centerMixedRowFactor_nonnegative (grade : ℕ) : 0 ≤ centerMixedRowFactor grade :=
  mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem centerMixedRows_integral_bound (mode : ℤ) (profile : ℝ → ComplexEuclidean 1)
    (smooth : ContDiffOn ℝ ∞ profile (Icc (1 / 2 : ℝ) 1)) (grade : ℕ) (bound : ℝ)
    (bounded : ∀ order, order ≤ grade → ∀ word : CartesianWord order,
      (∫ time in (0 : ℝ)..(1 / 2 : ℝ), ‖centerWordRows profile order word mode time‖ ^ 2) ≤ bound) :
    (∫ time in (0 : ℝ)..(1 / 2 : ℝ), mixedRowsDensity {mode} (centerWordRows profile) grade time) ≤
      centerMixedRowFactor grade * bound := by
  have wordContinuous (order : ℕ) (word : CartesianWord order) : ContinuousOn
      (fun time => ‖centerWordRows profile order word mode time‖ ^ 2) (Icc (0 : ℝ) (1 / 2)) :=
    (centerWordRows_continuousOn profile smooth order word mode).norm.pow 2
  have orderContinuous (order : ℕ) : ContinuousOn
      (mixedRowDensity {mode} (centerWordRows profile) order) (Icc (0 : ℝ) (1 / 2)) := by
    unfold mixedRowDensity
    simp only [Finset.sum_singleton]
    exact continuousOn_const.mul (continuousOn_finsetSum _ (fun word _ => continuousOn_const.mul (wordContinuous order word)))
  have wordWeightedContinuous (order : ℕ) (word : CartesianWord order) : ContinuousOn
      (fun time => ‖productWordCoefficient word‖ * ‖centerWordRows profile order word mode time‖ ^ 2)
      (Icc (0 : ℝ) (1 / 2)) := continuousOn_const.mul (wordContinuous order word)
  have orderBound (order : ℕ) (paid : order ≤ grade) :
      (∫ time in (0 : ℝ)..(1 / 2 : ℝ), mixedRowDensity {mode} (centerWordRows profile) order time) ≤
        productWordCoefficientSum order ^ 2 * bound := by
    unfold mixedRowDensity
    simp only [Finset.sum_singleton]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
      (fun word _ => ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
        (wordWeightedContinuous order word))]
    have comparison : (∑ word : CartesianWord order,
        ∫ time in (0 : ℝ)..(1 / 2 : ℝ), ‖productWordCoefficient word‖ * ‖centerWordRows profile order word mode time‖ ^ 2) ≤
        (∑ word : CartesianWord order, ‖productWordCoefficient word‖) * bound := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro word _
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (bounded order paid word) (norm_nonneg _)
    exact (mul_le_mul_of_nonneg_left comparison (productWordCoefficientSum_nonnegative order)).trans_eq (by
      unfold productWordCoefficientSum
      ring)
  unfold mixedRowsDensity
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
    (fun order _ => ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (orderContinuous order))]
  exact (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun order member =>
    orderBound order (by have := Finset.mem_range.mp member; omega))) (by positivity : 0 ≤ 2 * Real.pi)).trans_eq (by
      unfold centerMixedRowFactor
      rw [← Finset.sum_mul]
      ring)

theorem pinnedCenter_mixedRows_bound (grade : ℕ) (large : 3 ≤ grade) (radius : ℝ)
    (mode : ℤ) (center : mode = 1 ∨ mode = -1) (frequency : ℝ) (bounded : |frequency| ≤ radius)
    (source : ClosedJet 1) (pure : angularClosedJet mode source = source) (order : ℕ) (paid : order ≤ grade + 2) :
    (∫ time in (0 : ℝ)..(1 / 2 : ℝ), mixedRowsDensity {mode}
      (centerWordRows (pureProfile mode (pinnedCenterSolution mode frequency source))) order time) ≤
        (2 * centerMixedRowFactor order * centerAllRadialConstant grade large radius) * ‖unitDiskCoreInto grade source‖ ^ 2 := by
  have estimate := centerMixedRows_integral_bound mode _ (pureProfile_smooth mode _).contDiffOn order
    (2 * (centerAllRadialConstant grade large radius * ‖unitDiskCoreInto grade source‖ ^ 2)) (by
      intro current currentBound word
      have counts := wordCount_total word
      exact (centerWordRow_radial_integral mode center _ (pureProfile_smooth mode _).contDiffOn current word).trans
        (mul_le_mul_of_nonneg_left (pinnedCenterProfile_allRadial grade large radius mode center frequency bounded source pure
          (wordCount word 0) (by omega)) (by norm_num)))
  exact estimate.trans_eq (by ring)

end Grad.ActualCenterBounds
