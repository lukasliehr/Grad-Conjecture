import ADZ10UniformHighComparison

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularUniformBoundary
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The outer trace constant is evaluated on the fixed terminal half collar,
so it is independent of the inner radius. -/
def uniformOuterTraceConstant (length : ℝ) : ℝ :=
  annularTraceConstant (1 / 2) length

theorem uniformOuterTraceConstant_nonnegative (length : ℝ) :
    0 ≤ uniformOuterTraceConstant length := Real.sqrt_nonneg _

/-- Restricting the actual AAG core energy to `[1/2,1]` can only lower it. -/
theorem halfAnnularModeEnergyCore_norm_le (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (mode : HighAnnularMode)
    (core : complexSmoothRadialCore 1) :
    ‖annularModeEnergyCore (1 / 2) length (by norm_num) mode.val.1 mode.val.2 core‖ ≤
      ‖annularModeEnergyCore lower length positive mode.val.1 mode.val.2 core‖ := by
  let integrand : ℝ → ℝ := fun radius => radius *
    (‖core.val.2 radius‖ ^ 2 +
      annularPotential length radius mode.val.1 mode.val.2 * ‖core.val.1 radius‖ ^ 2)
  have lowerOne : lower ≤ 1 := lowerHalf.trans (by norm_num)
  have integrable : IntervalIntegrable integrand volume lower 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le lowerOne]
    exact continuousOn_id.mul ((core.val.2.continuous.norm.pow 2).continuousOn.add
      ((annularPotential_continuousOn lower length positive mode.val.1 mode.val.2).mul
        (core.val.1.continuous.norm.pow 2).continuousOn))
  have nonnegative : ∀ radius ∈ Icc lower 1, 0 ≤ integrand radius := by
    intro radius inside
    have radiusPositive := positive.trans_le inside.1
    exact mul_nonneg radiusPositive.le (add_nonneg (sq_nonneg _)
      (mul_nonneg (annularPotential_pos length radius mode.val.1 mode.val.2 mode.property
        radiusPositive).le (sq_nonneg _)))
  have restricted : (∫ radius in (1 / 2 : ℝ)..1, integrand radius) ≤
      ∫ radius in lower..1, integrand radius := by
    apply intervalIntegral.integral_mono_interval lowerHalf (by norm_num) le_rfl
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius inside
      exact nonnegative radius ⟨inside.1.le, inside.2⟩
    · exact integrable
  have halfSq := annularModeEnergyCore_norm_sq (1 / 2) length (by norm_num)
    (by norm_num) mode.val.1 mode.val.2 core
  have fullSq := annularModeEnergyCore_norm_sq lower length positive lowerOne
    mode.val.1 mode.val.2 core
  change ‖annularModeEnergyCore (1 / 2) length (by norm_num) mode.val.1 mode.val.2 core‖ ^ 2 =
    (∫ radius in (1 / 2 : ℝ)..1, integrand radius) + 2 * ‖core.val.1 1‖ ^ 2 at halfSq
  change ‖annularModeEnergyCore lower length positive mode.val.1 mode.val.2 core‖ ^ 2 =
    (∫ radius in lower..1, integrand radius) + 2 * ‖core.val.1 1‖ ^ 2 at fullSq
  nlinarith [norm_nonneg (annularModeEnergyCore (1 / 2) length (by norm_num)
      mode.val.1 mode.val.2 core),
    norm_nonneg (annularModeEnergyCore lower length positive mode.val.1 mode.val.2 core)]

/-- The literal frequency-normalized outer value is uniformly bounded by the
actual one-mode AAG energy, with a constant depending only on `length`. -/
theorem annularModeEnergyCore_outer_uniform (lower length : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length) (mode : HighAnnularMode)
    (core : complexSmoothRadialCore 1) :
    ‖(Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) • core.val.1 1‖ ≤
      uniformOuterTraceConstant length *
        ‖annularModeEnergyCore lower length positive mode.val.1 mode.val.2 core‖ := by
  have fixed := annularModeEnergyCore_endpoint_bound (1 / 2) length (by norm_num)
    (by norm_num) lengthPositive mode core 1
  exact fixed.trans (mul_le_mul_of_nonneg_left
    (halfAnnularModeEnergyCore_norm_le lower length positive lowerHalf mode core)
    (uniformOuterTraceConstant_nonnegative length))

end Grad.AnnularUniformBoundary
