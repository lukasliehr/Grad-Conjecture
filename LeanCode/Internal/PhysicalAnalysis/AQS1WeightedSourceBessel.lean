import AQR6ActualSecondRadialConsumer

noncomputable section
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.AnnularSourceGraph Grad.SourceCollarDivision

/-- The actual angular-power coefficient law gives the literal weighted
radial L2 energy, with ordinary area and the accepted r dr storage. -/
theorem diskL2Radial_angularPower_energy (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
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

private theorem source_energy_transfer (energy radial constant image size : ℝ)
    (nonnegative : 0 ≤ image) (collective : energy ≤ radial ^ 2 * image ^ 2)
    (bound : image ≤ constant * size) : energy ≤ (radial * constant) ^ 2 * size ^ 2 :=
  collective.trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ nonnegative bound 2)
    (sq_nonneg radial)).trans_eq (by ring))

/-- Collective weighted forcing bound from the completed ordinary Hs source.
Its constant is independent of the angular set and collar endpoint. -/
theorem ordinarySource_weighted_radial_finite (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (order : ℕ) (source : unitDiskSobolev order) (modes : Finset ℤ) :
    (∑ mode ∈ modes, |(mode : ℝ)| ^ (2 * order) *
      ‖diskL2Radial lower positive bounded mode (unitDiskBulk order source)‖ ^ 2) ≤
      (diskRadialL2Bound * unitRotationPowerConstant order) ^ 2 * ‖source‖ ^ 2 := by
  let derivative : DiskL2 1 := sourceRotationPower order source.val
  have each (mode : ℤ) : ‖diskL2Radial lower positive bounded mode derivative‖ ^ 2 =
      |(mode : ℝ)| ^ (2 * order) * ‖diskL2Radial lower positive bounded mode (unitDiskBulk order source)‖ ^ 2 :=
    diskL2Radial_angularPower_energy lower positive bounded order (unitDiskBulk order source) derivative mode
      (sourceRotationPower_coefficient order mode source.val)
  have same := Finset.sum_congr (s₁ := modes) rfl (fun mode _ => (each mode).symm)
  have collective : (∑ mode ∈ modes, |(mode : ℝ)| ^ (2 * order) *
      ‖diskL2Radial lower positive bounded mode (unitDiskBulk order source)‖ ^ 2) ≤
      diskRadialL2Bound ^ 2 * ‖derivative‖ ^ 2 :=
    same.trans_le (diskL2Radial_finite_energy lower positive bounded derivative modes)
  exact source_energy_transfer _ diskRadialL2Bound (unitRotationPowerConstant order) ‖derivative‖ ‖source‖
    (norm_nonneg _) collective (sourceRotationPower_bound order source.val)

end Grad.CircularHighRegularity
