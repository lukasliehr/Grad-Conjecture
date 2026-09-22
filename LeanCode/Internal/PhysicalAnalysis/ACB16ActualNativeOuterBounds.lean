import ACB15CenterMixedRowEnergy

noncomputable section
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators Interval
namespace Grad.ActualCenterBounds
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.ActualCenterVolterra Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.CollarCartesian Grad.GaugeCoefficients.Algebra

def centerOuterRowConstant (index : CartesianMultiIndex) : ℝ := (centerOuterJet_mixedRows_bound index).choose

theorem centerOuterRowConstant_nonnegative (index : CartesianMultiIndex) : 0 ≤ centerOuterRowConstant index :=
  (centerOuterJet_mixedRows_bound index).choose_spec.1

def centerOuterNativeFactor (grade : ℕ) : ℝ :=
  ∑ index : DerivativeIndex grade, 2 * centerOuterRowConstant (derivativeMultiIndex index) *
    centerMixedRowFactor (cartesianOrder (derivativeMultiIndex index))

theorem centerOuterNativeFactor_nonnegative (grade : ℕ) : 0 ≤ centerOuterNativeFactor grade :=
  Finset.sum_nonneg (fun index _ => mul_nonneg
    (mul_nonneg (by norm_num) (centerOuterRowConstant_nonnegative _)) (centerMixedRowFactor_nonnegative _))

/-- Every original Cartesian row of the actual outer center solution is
controlled at the requested grade; constants have no source dependence. -/
theorem pinnedCenter_outer_native_squared (grade : ℕ) (large : 3 ≤ grade) (radius : ℝ)
    (mode : ℤ) (center : mode = 1 ∨ mode = -1) (frequency : ℝ) (bounded : |frequency| ≤ radius)
    (source : ClosedJet 1) (pure : angularClosedJet mode source = source) (target : ℕ) (paid : target ≤ grade + 2) :
    ‖unitDiskCoreInto target (centerOuterJet mode (pinnedCenterSolution mode frequency source))‖ ^ 2 ≤
      (centerOuterNativeFactor target * centerAllRadialConstant grade large radius) * ‖unitDiskCoreInto grade source‖ ^ 2 := by
  rw [unitDiskSobolev_norm_sq]
  simp only [unitDiskDerivative_core]
  unfold centerOuterNativeFactor
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index _
  have row := (centerOuterJet_mixedRows_bound (derivativeMultiIndex index)).choose_spec.2
    mode (pinnedCenterSolution mode frequency source)
  have estimate := row.trans (mul_le_mul_of_nonneg_left
    (pinnedCenter_mixedRows_bound grade large radius mode center frequency bounded source pure
      (cartesianOrder (derivativeMultiIndex index)) (le_trans index.property paid))
    (centerOuterRowConstant_nonnegative _))
  exact estimate.trans_eq (by unfold centerOuterRowConstant; ring)

def centerOuterConstant (grade : ℕ) (large : 3 ≤ grade) (radius : ℝ) (target : ℕ) : ℝ :=
  Real.sqrt (centerOuterNativeFactor target * centerAllRadialConstant grade large radius)

theorem centerOuterConstant_nonnegative (grade : ℕ) (large : 3 ≤ grade) (radius : ℝ) (target : ℕ) :
    0 ≤ centerOuterConstant grade large radius target := Real.sqrt_nonneg _

private theorem nonnegative_root_bound (value constant size : ℝ) (valueNonnegative : 0 ≤ value)
    (constantNonnegative : 0 ≤ constant) (sizeNonnegative : 0 ≤ size)
    (bound : value ^ 2 ≤ constant * size ^ 2) : value ≤ Real.sqrt constant * size := by
  apply (sq_le_sq₀ valueNonnegative (mul_nonneg (Real.sqrt_nonneg constant) sizeNonnegative)).mp
  rwa [mul_pow, Real.sq_sqrt constantNonnegative]

theorem pinnedCenter_outer_native (grade : ℕ) (large : 3 ≤ grade) (radius : ℝ)
    (mode : ℤ) (center : mode = 1 ∨ mode = -1) (frequency : ℝ) (bounded : |frequency| ≤ radius)
    (source : ClosedJet 1) (pure : angularClosedJet mode source = source) (target : ℕ) (paid : target ≤ grade + 2) :
    ‖unitDiskCoreInto target (centerOuterJet mode (pinnedCenterSolution mode frequency source))‖ ≤
      centerOuterConstant grade large radius target * ‖unitDiskCoreInto grade source‖ := by
  exact nonnegative_root_bound _ _ _ (norm_nonneg _)
    (mul_nonneg (centerOuterNativeFactor_nonnegative target) (centerAllRadialConstant_nonnegative grade large radius))
    (norm_nonneg _) (pinnedCenter_outer_native_squared grade large radius mode center frequency bounded source pure target paid)

end Grad.ActualCenterBounds
