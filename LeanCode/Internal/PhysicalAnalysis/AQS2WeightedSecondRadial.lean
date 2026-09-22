import AQS1WeightedSourceBessel

noncomputable section
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.AnnularSourceGraph Grad.SourceCollarDivision

private theorem zeroOne_weight_scalar (mode value slope : ℝ) (order : ℕ) :
    mode ^ (2 * order) * (mode ^ 4 * value + mode ^ 2 * slope) =
      mode ^ (2 * (order + 2)) * value + mode ^ (2 * (order + 1)) * slope := by
  have four : 2 * (order + 2) = 2 * order + 4 := by omega
  have two : 2 * (order + 1) = 2 * order + 2 := by omega
  rw [four, two, pow_add, pow_add]
  ring

theorem inverseZeroOneEnergy_weight (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameter : ℝ) (order : ℕ) (source : highDiskL2) (mode : ℤ) :
    |(mode : ℝ)| ^ (2 * order) * inverseZeroOneEnergy lower positive bounded parameter 0 source mode =
      inverseZeroOneEnergy lower positive bounded parameter order source mode :=
  zeroOne_weight_scalar |(mode : ℝ)|
    (‖diskL2Radial lower positive bounded mode (highDiskBulk (highRobinWeakInverse parameter source))‖ ^ 2)
    (‖weightedRadialCoordinate 1 lower 1
      (diskRadial lower positive bounded mode (highRobinWeakInverse parameter source).val)‖ ^ 2) order

private theorem scale_second_bound (weight energy factor zeroOne forcing : ℝ) (nonnegative : 0 ≤ weight)
    (bound : energy ≤ 4 * (factor * zeroOne + forcing)) :
    weight * energy ≤ 4 * (factor * (weight * zeroOne) + weight * forcing) :=
  (mul_le_mul_of_nonneg_left bound nonnegative).trans_eq (by ring)

/-- The AN19 second derivative carries every source-grade angular weight;
the original source coefficient, inverse and radial interval are unchanged. -/
theorem actualSecondRadialEnergy_weighted (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (order : ℕ) (source : highDiskL2) (core : ClosedJet 1)
    (same : source.val = closedL2Core core) (mode : ℤ) (high : mode ∉ lowAngularModes) :
    |(mode : ℝ)| ^ (2 * order) * actualSecondRadialEnergy lower positive bounded parameter source core mode ≤
      4 * (secondRadialFactor lower parameter * inverseZeroOneEnergy lower positive bounded.le parameter order source mode +
        |(mode : ℝ)| ^ (2 * order) * ‖diskL2Radial lower positive bounded.le mode source.val‖ ^ 2) := by
  let forcing : ℝ := ‖diskL2Radial lower positive bounded.le mode source.val‖ ^ 2
  have scaled : |(mode : ℝ)| ^ (2 * order) * actualSecondRadialEnergy lower positive bounded parameter source core mode ≤
      4 * (secondRadialFactor lower parameter *
        (|(mode : ℝ)| ^ (2 * order) * inverseZeroOneEnergy lower positive bounded.le parameter 0 source mode) +
        |(mode : ℝ)| ^ (2 * order) * forcing) :=
    scale_second_bound (|(mode : ℝ)| ^ (2 * order))
      (actualSecondRadialEnergy lower positive bounded parameter source core mode)
      (secondRadialFactor lower parameter) (inverseZeroOneEnergy lower positive bounded.le parameter 0 source mode)
      forcing (pow_nonneg (abs_nonneg _) _) (actualSecondRadialEnergy_zeroOne lower positive bounded parameter source core same mode high)
  exact scaled.trans_eq (congrArg (fun energy : ℝ =>
    4 * (secondRadialFactor lower parameter * energy + |(mode : ℝ)| ^ (2 * order) * forcing))
    (inverseZeroOneEnergy_weight lower positive bounded.le parameter order source mode))

def weightedSecondRadialConstant (lower parameter : ℝ) (order : ℕ) : ℝ :=
  4 * (secondRadialFactor lower parameter * zeroOneCollarConstant order +
    (diskRadialL2Bound * unitRotationPowerConstant order) ^ 2)

theorem weightedSecondRadialConstant_nonnegative (lower parameter : ℝ) (order : ℕ) :
    0 ≤ weightedSecondRadialConstant lower parameter order :=
  mul_nonneg (by norm_num) (add_nonneg
    (mul_nonneg (secondRadialFactor_nonnegative lower parameter) (zeroOneCollarConstant_nonnegative order)) (sq_nonneg _))

private theorem finite_weighted_second_bound (modes : Finset ℤ) (energy zeroOne forcing : ℤ → ℝ)
    (factor zeroConstant forceConstant size : ℝ) (factorNonnegative : 0 ≤ factor)
    (pointwise : ∀ mode ∈ modes, energy mode ≤ 4 * (factor * zeroOne mode + forcing mode))
    (zeroBound : (∑ mode ∈ modes, zeroOne mode) ≤ zeroConstant * size ^ 2)
    (forceBound : (∑ mode ∈ modes, forcing mode) ≤ forceConstant * size ^ 2) :
    (∑ mode ∈ modes, energy mode) ≤ 4 * (factor * zeroConstant + forceConstant) * size ^ 2 := by
  have pointwiseSum := Finset.sum_le_sum pointwise
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum] at pointwiseSum
  exact pointwiseSum.trans ((mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left zeroBound factorNonnegative) forceBound)
    (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by ring))

theorem actualSecondRadial_weighted_finite (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (order : ℕ) (source : unitDiskSobolev order)
    (high : unitDiskBulk order source ∈ highDiskL2) (core : ClosedJet 1)
    (same : unitDiskBulk order source = closedL2Core core)
    (modes : Finset ℤ) (highModes : ∀ mode ∈ modes, mode ∉ lowAngularModes) :
    (∑ mode ∈ modes, |(mode : ℝ)| ^ (2 * order) * actualSecondRadialEnergy lower positive bounded parameter
      ⟨unitDiskBulk order source, high⟩ core mode) ≤ weightedSecondRadialConstant lower parameter order * ‖source‖ ^ 2 :=
  finite_weighted_second_bound modes
    (fun mode => |(mode : ℝ)| ^ (2 * order) * actualSecondRadialEnergy lower positive bounded parameter
      ⟨unitDiskBulk order source, high⟩ core mode)
    (inverseZeroOneEnergy lower positive bounded.le parameter order ⟨unitDiskBulk order source, high⟩)
    (fun mode => |(mode : ℝ)| ^ (2 * order) * ‖diskL2Radial lower positive bounded.le mode (unitDiskBulk order source)‖ ^ 2)
    (secondRadialFactor lower parameter) (zeroOneCollarConstant order)
    ((diskRadialL2Bound * unitRotationPowerConstant order) ^ 2) ‖source‖
    (secondRadialFactor_nonnegative lower parameter)
    (fun mode member => actualSecondRadialEnergy_weighted lower positive bounded parameter order
      ⟨unitDiskBulk order source, high⟩ core same mode (highModes mode member))
    (weakInverse_zeroOne_finite lower positive bounded.le parameter order source high modes)
    (ordinarySource_weighted_radial_finite lower positive bounded.le order source modes)

end Grad.CircularHighRegularity
