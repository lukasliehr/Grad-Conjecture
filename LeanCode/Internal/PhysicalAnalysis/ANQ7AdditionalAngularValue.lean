import ANQ6CollectiveRadialL2
import ANQ5ActualAngularCollarEstimate

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarDivision Grad.AnnularSourceGraph

theorem highRotation_power_coefficient (order : ℕ) (field derivative : highDiskGrade)
    (modeLaw : ∀ mode, highDiskMode mode derivative =
      (Complex.I * (mode : ℂ)) ^ order • highDiskMode mode field) (mode : ℤ) :
    diskMode mode (highRotation derivative) =
      (Complex.I * (mode : ℂ)) ^ (order + 1) • diskMode mode (highDiskBulk field) := by
  let scalar := Complex.I * (mode : ℂ)
  have coefficient := (highDiskMode_bulk mode derivative).symm.trans
    ((congrArg highDiskBulk (modeLaw mode)).trans
      ((highDiskBulk.map_smul (scalar ^ order) (highDiskMode mode field)).trans
        (congrArg (fun value : DiskL2 1 => scalar ^ order • value) (highDiskMode_bulk mode field))))
  exact (highRotation_coefficient mode derivative).trans
    ((congrArg (fun value : DiskL2 1 => scalar • value) coefficient).trans
      ((smul_smul _ _ _).trans (congrArg (fun value : ℂ => value • diskMode mode (highDiskBulk field))
        (pow_succ' scalar order).symm)))

private theorem radialL2_power_energy (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (order : ℕ) (field derivative : DiskL2 1) (mode : ℤ)
    (coefficient : diskMode mode derivative = (Complex.I * (mode : ℂ)) ^ order • diskMode mode field) :
    ‖diskL2Radial lower positive bounded mode derivative‖ ^ 2 =
      |(mode : ℝ)| ^ (2 * order) * ‖diskL2Radial lower positive bounded mode field‖ ^ 2 := by
  have exactCoefficient := (diskL2Radial_mode_self lower positive bounded mode derivative).symm.trans
    ((congrArg (diskL2Radial lower positive bounded mode) coefficient).trans
      (((diskL2Radial lower positive bounded mode).map_smul _ _).trans
        (congrArg (fun value : RadialL2 1 lower => (Complex.I * (mode : ℂ)) ^ order • value)
          (diskL2Radial_mode_self lower positive bounded mode field))))
  have integer : ‖(mode : ℂ)‖ = |(mode : ℝ)| := by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  have scalar : ‖(Complex.I * (mode : ℂ)) ^ order‖ ^ 2 = |(mode : ℝ)| ^ (2 * order) := by
    rw [norm_pow, norm_mul, Complex.norm_I, one_mul, integer, ← pow_mul, Nat.mul_comm order 2]
  exact (congrArg (fun value : RadialL2 1 lower => ‖value‖ ^ 2) exactCoefficient).trans
    (by rw [norm_smul, mul_pow, scalar])

/-- The H1 angular derivative supplies one further angular derivative of
the value in L2, using the literal Cartesian rotation and its gradient bound. -/
theorem diskRadial_additional_value_finite (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (order : ℕ) (field derivative : highDiskGrade)
    (modeLaw : ∀ mode, highDiskMode mode derivative =
      (Complex.I * (mode : ℂ)) ^ order • highDiskMode mode field) (modes : Finset ℤ) :
    (∑ mode ∈ modes, |(mode : ℝ)| ^ (2 * (order + 1)) *
      ‖diskL2Radial lower positive bounded mode (highDiskBulk field)‖ ^ 2) ≤
      diskRadialL2Bound ^ 2 * ‖derivative‖ ^ 2 := by
  have each (mode : ℤ) := radialL2_power_energy lower positive bounded (order + 1)
    (highDiskBulk field) (highRotation derivative) mode
    (highRotation_power_coefficient order field derivative modeLaw mode)
  have equality := Finset.sum_congr (s₁ := modes) rfl (fun mode _ => (each mode).symm)
  have collective := diskL2Radial_finite_energy lower positive bounded (highRotation derivative) modes
  have rotation := pow_le_pow_left₀ (norm_nonneg _) (highRotation_contract derivative) 2
  exact equality.trans_le (collective.trans (mul_le_mul_of_nonneg_left rotation (sq_nonneg _)))

end Grad.CircularHighRegularity
