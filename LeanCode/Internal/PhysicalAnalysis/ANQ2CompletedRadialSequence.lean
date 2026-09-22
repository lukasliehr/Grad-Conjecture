import ANQ1CollectiveRadialEnergy

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak
open Grad.AnnularSourceGraph

/-- All actual radial H1 coefficients in one square-summable carrier.
Membership comes from the collective Bessel estimate, not singleton bounds. -/
def diskRadialSequenceLinear (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    diskGrade →ₗ[ℝ] lp (fun _ : ℤ => WeightedRadialH1 1 lower) 2 where
  toFun field := ⟨fun mode => diskRadial lower positive bounded mode field, by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
    exact diskRadial_summable_energy lower positive bounded field⟩
  map_add' first second := by
    apply lp.ext
    funext mode
    exact (diskRadial lower positive bounded mode).map_add first second
  map_smul' scalar field := by
    apply lp.ext
    funext mode
    exact (diskRadial lower positive bounded mode).map_smul scalar field

theorem diskRadialSequenceLinear_norm_sq (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : diskGrade) :
    ‖diskRadialSequenceLinear lower positive bounded field‖ ^ 2 =
      ∑' mode : ℤ, ‖diskRadial lower positive bounded mode field‖ ^ 2 := by
  have formula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (diskRadialSequenceLinear lower positive bounded field)
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at formula
  exact formula

theorem diskRadialSequenceLinear_bound (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : diskGrade) :
    ‖diskRadialSequenceLinear lower positive bounded field‖ ≤ diskRadialBound * ‖field‖ := by
  have energy := (diskRadialSequenceLinear_norm_sq lower positive bounded field).trans_le
    (diskRadial_total_energy lower positive bounded field)
  have nonnegative := mul_nonneg diskRadialBound_nonnegative (norm_nonneg field)
  nlinarith [sq_nonneg (‖diskRadialSequenceLinear lower positive bounded field‖ - diskRadialBound * ‖field‖)]

def diskRadialSequence (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    diskGrade →L[ℝ] lp (fun _ : ℤ => WeightedRadialH1 1 lower) 2 :=
  (diskRadialSequenceLinear lower positive bounded).mkContinuous diskRadialBound
    (diskRadialSequenceLinear_bound lower positive bounded)

theorem diskRadialSequence_apply (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : diskGrade) (mode : ℤ) :
    diskRadialSequence lower positive bounded field mode = diskRadial lower positive bounded mode field := rfl

/-- Actual AN18 consumer in the collective radial H1 norm, uniform in
every angular cutoff and every real parameter. -/
theorem weakInverse_collective_radial_bound (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameter : ℝ) (source : highDiskL2) :
    ‖diskRadialSequence lower positive bounded (highRobinWeakInverse parameter source).val‖ ≤
      (2 * diskRadialBound) * ‖source‖ := by
  have bound := diskRadialSequenceLinear_bound lower positive bounded (highRobinWeakInverse parameter source).val
  have inverse := weakSolution_bound parameter source
  exact bound.trans ((mul_le_mul_of_nonneg_left inverse diskRadialBound_nonnegative).trans_eq (by ring))

end Grad.CircularHighRegularity
