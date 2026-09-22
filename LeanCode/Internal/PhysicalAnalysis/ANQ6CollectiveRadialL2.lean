import ANQ3RadialAngularCompatibility

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak
open Grad.SourceCollarDivision Grad.AnnularSourceGraph

theorem diskMode_summable_energy (field : DiskL2 1) :
    Summable (fun mode : ℤ => ‖diskMode mode field‖ ^ 2) := by
  have finite := (memℓp_gen_iff (p := 2) (by norm_num)).1 (lp.memℓp (diskFourier field))
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at finite
  exact finite

theorem diskMode_total_energy (field : DiskL2 1) :
    (∑' mode : ℤ, ‖diskMode mode field‖ ^ 2) = ‖field‖ ^ 2 := by
  have formula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (diskFourier field)
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at formula
  exact formula.symm.trans (congrArg (fun value : ℝ => value ^ 2) (diskFourier_norm field))

theorem diskMode_finite_energy (field : DiskL2 1) (modes : Finset ℤ) :
    (∑ mode ∈ modes, ‖diskMode mode field‖ ^ 2) ≤ ‖field‖ ^ 2 :=
  ((diskMode_summable_energy field).sum_le_tsum modes (fun _ _ => sq_nonneg _)).trans_eq
    (diskMode_total_energy field)

/-- Collective radial extraction from arbitrary ordinary-area disk L2.
Parseval retains all angular modes and supplies the original 1/(2π) normalization. -/
theorem diskL2Radial_finite_energy (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : DiskL2 1) (modes : Finset ℤ) :
    (∑ mode ∈ modes, ‖diskL2Radial lower positive bounded mode field‖ ^ 2) ≤
      diskRadialL2Bound ^ 2 * ‖field‖ ^ 2 := by
  have each (mode : ℤ) : ‖diskL2Radial lower positive bounded mode field‖ ^ 2 ≤
      diskRadialL2Bound ^ 2 * ‖diskMode mode field‖ ^ 2 := by
    have squared := pow_le_pow_left₀ (norm_nonneg _)
      (diskL2Radial_bound lower positive bounded mode (diskMode mode field)) 2
    have same := congrArg (fun radial : RadialL2 1 lower => ‖radial‖ ^ 2)
      (diskL2Radial_mode_self lower positive bounded mode field)
    exact same.symm.trans_le (squared.trans_eq (mul_pow _ _ _))
  have summed := Finset.sum_le_sum (s := modes) (fun mode _ => each mode)
  rw [← Finset.mul_sum] at summed
  exact summed.trans (mul_le_mul_of_nonneg_left (diskMode_finite_energy field modes) (sq_nonneg _))

theorem diskL2Radial_summable_energy (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : DiskL2 1) : Summable (fun mode : ℤ => ‖diskL2Radial lower positive bounded mode field‖ ^ 2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) (diskL2Radial_finite_energy lower positive bounded field)

theorem diskL2Radial_total_energy (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : DiskL2 1) :
    (∑' mode : ℤ, ‖diskL2Radial lower positive bounded mode field‖ ^ 2) ≤ diskRadialL2Bound ^ 2 * ‖field‖ ^ 2 :=
  (diskL2Radial_summable_energy lower positive bounded field).tsum_le_of_sum_le
    (diskL2Radial_finite_energy lower positive bounded field)

end Grad.CircularHighRegularity
