import AKN7FullCircleDecay

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.ExhaustionSourceAllocation

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.SourceCollarDivision
open Grad.NonlinearRadial Grad.BoundaryTrace

theorem sourceCircleCoefficient_continuous {dimension : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension) (mode : ℤ) :
    Continuous (fun radius => sourceCircleCoefficient parameters cell field radius mode) :=
  (radialCoefficientJet_smooth _ (polarTaylorRemainder_smooth 0 _) mode 0).continuous

theorem sourceCircleEnergy_continuous {dimension : ℕ} (parameters : PhaseParameters)
    (power : ℕ) (field : ACore parameters dimension) (mode : ℤ × ℤ) :
    Continuous (fun radius => sourceCircleEnergy parameters power field radius mode) :=
  continuous_const.mul ((sourceCircleCoefficient_continuous parameters mode.2 (field.val mode.2) mode.1).norm.pow 2)

/-- Actual BF bulk density, with an optional original division by r.
Clamping only supplies a continuous extension outside the moving collar. -/
def sourceTiltDensity (lower : ℝ) (division : ℕ) (radius : ℝ) : ℝ :=
  (max lower radius) ^ (-7 / 2 - 2 * (division : ℝ))

theorem sourceTiltDensity_continuous (lower : ℝ) (positive : 0 < lower) (division : ℕ) :
    Continuous (sourceTiltDensity lower division) :=
  (continuous_const.max continuous_id).rpow_const
    (fun radius => Or.inl (positive.trans_le (le_max_left lower radius)).ne')

theorem sourceTiltDensity_same (lower : ℝ) (division : ℕ) (radius : ℝ) (inside : lower ≤ radius) :
    sourceTiltDensity lower division radius = radius ^ (-7 / 2 - 2 * (division : ℝ)) := by
  rw [sourceTiltDensity, max_eq_right inside]

theorem sourceTiltDensity_decay (lower radius : ℝ) (positive : 0 < lower)
    (inside : radius ∈ Icc lower 1) (depth division : ℕ) (vanishing : division + 2 ≤ depth) :
    sourceTiltDensity lower division radius * radius ^ (2 * depth) ≤ 1 := by
  have radialPositive := positive.trans_le inside.1
  rw [sourceTiltDensity_same lower division radius inside.1,
    ← Real.rpow_natCast, ← Real.rpow_add radialPositive]
  apply Real.rpow_le_one radialPositive.le inside.2
  have payment : (division : ℝ) + 2 ≤ depth := by exact_mod_cast vanishing
  push_cast
  linarith

def sourceTiltModeEnergy {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (division power : ℕ) (field : ACore parameters dimension) (mode : ℤ × ℤ) : ℝ :=
  ∫ radius in lower..1, sourceTiltDensity lower division radius * sourceCircleEnergy parameters power field radius mode

theorem sourceTiltModeEnergy_nonnegative {dimension : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (division power : ℕ) (field : ACore parameters dimension) (mode : ℤ × ℤ) :
    0 ≤ sourceTiltModeEnergy parameters lower division power field mode := by
  apply intervalIntegral.integral_nonneg bounded
  intro radius _
  exact mul_nonneg (Real.rpow_nonneg (positive.trans_le (le_max_left _ _)).le _)
    (sourceCircleEnergy_nonnegative parameters power field radius mode)

/-- Uniform integral bound for the actual tilted bulk density. In the
worst cases (depth,division)=(2,0) and (3,1), the remaining power is r^(1/2). -/
theorem finite_sourceTilt_bound {dimension grade depth power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (flat : ∀ cell, VanishingJets depth (field.val cell)) (paid : depth + power + 2 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (division : ℕ) (vanishing : division + 2 ≤ depth) (modes : Finset (ℤ × ℤ)) :
    (∑ mode ∈ modes, sourceTiltModeEnergy parameters lower division power field mode) ≤
      remainderAngularBoundConstant depth power 0 * ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2 := by
  let bound := remainderAngularBoundConstant depth power 0 * ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2
  have boundNonnegative : 0 ≤ bound := mul_nonneg (remainderAngularBoundConstant_nonnegative _ _ _) (sq_nonneg _)
  have continuousTerm (mode : ℤ × ℤ) : Continuous (fun radius =>
      sourceTiltDensity lower division radius * sourceCircleEnergy parameters power field radius mode) :=
    (sourceTiltDensity_continuous lower positive division).mul (sourceCircleEnergy_continuous parameters power field mode)
  have continuousSum := continuous_finsetSum modes (fun mode _ => continuousTerm mode)
  have pointBound (radius : ℝ) (inside : radius ∈ Icc lower 1) :
      (∑ mode ∈ modes, sourceTiltDensity lower division radius * sourceCircleEnergy parameters power field radius mode) ≤ bound := by
    rw [← Finset.mul_sum]
    have densityNonnegative : 0 ≤ sourceTiltDensity lower division radius :=
      Real.rpow_nonneg (positive.trans_le (le_max_left _ _)).le _
    have circle := finite_fullCircle_decay parameters field flat paid radius (positive.trans_le inside.1).le inside.2 modes
    calc
      _ ≤ sourceTiltDensity lower division radius *
          (radius ^ (2 * depth) * remainderAngularBoundConstant depth power 0 *
            ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2) := mul_le_mul_of_nonneg_left circle densityNonnegative
      _ = (sourceTiltDensity lower division radius * radius ^ (2 * depth)) * bound := by dsimp only [bound]; ring
      _ ≤ bound := mul_le_of_le_one_left boundNonnegative (sourceTiltDensity_decay lower radius positive inside depth division vanishing)
  calc
    _ = ∫ radius in lower..1, ∑ mode ∈ modes,
        sourceTiltDensity lower division radius * sourceCircleEnergy parameters power field radius mode := by
      rw [intervalIntegral.integral_finsetSum (fun mode _ => (continuousTerm mode).intervalIntegrable _ _)]
      rfl
    _ ≤ ∫ _radius in lower..1, bound := intervalIntegral.integral_mono_on bounded
      (continuousSum.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _) pointBound
    _ = (1 - lower) * bound := by rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ bound := mul_le_of_le_one_left boundNonnegative (by linarith)

theorem full_sourceTilt_bound {dimension grade depth power : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (flat : ∀ cell, VanishingJets depth (field.val cell)) (paid : depth + power + 2 ≤ grade)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (division : ℕ) (vanishing : division + 2 ≤ depth) :
    (∑' mode : ℤ × ℤ, sourceTiltModeEnergy parameters lower division power field mode) ≤
      remainderAngularBoundConstant depth power 0 * ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2 :=
  Real.tsum_le_of_sum_le (sourceTiltModeEnergy_nonnegative parameters lower positive bounded division power field)
    (finite_sourceTilt_bound parameters field flat paid lower positive bounded division vanishing)

end Grad.ExhaustionSourceAllocation
