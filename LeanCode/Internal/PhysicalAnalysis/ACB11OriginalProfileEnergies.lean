import ACB10GenericCollarRecurrence

noncomputable section
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators Interval
namespace Grad.ActualCenterBounds
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.ActualCenterVolterra Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.OrdinarySourceRadial Grad.OrdinaryDiskCalculus
open Grad.GaugeCoefficients.Physical.RadialLedger (apLoweringConstant apLoweringConstant_nonnegative)

theorem pureProfile_energy_eq (field : ClosedJet 1) (mode : ℤ) (order : ℕ)
    (lower : ℝ) (nonnegative : 0 ≤ lower) (bounded : lower < 1) :
    radialWithinEnergy lower order (pureProfile mode field) =
      annularCoefficientEnergy lower (radialIter order (originalPolarValue field)) mode := by
  rw [sourceRadial_energy_within field mode order lower bounded, radialWithinEnergy]
  apply intervalIntegral.integral_congr
  intro radius inside
  have member : radius ∈ Icc lower 1 := by simpa only [uIcc_of_le bounded.le] using inside
  dsimp only
  rw [pureProfile_within_derivative mode field order lower nonnegative radius member]

theorem pureProfile_energy_native (grade order : ℕ) (paid : order ≤ grade)
    (field : ClosedJet 1) (mode : ℤ) (lower : ℝ) (nonnegative : 0 ≤ lower) (bounded : lower < 1) :
    radialWithinEnergy lower order (pureProfile mode field) ≤
      ((2 * Real.pi)⁻¹ * polarOrderConstant order) * ‖unitDiskCoreInto grade field‖ ^ 2 := by
  rw [pureProfile_energy_eq field mode order lower nonnegative bounded]
  have estimate := ordinaryRadial_finite_energy grade order 0 (by omega) field lower nonnegative bounded.le {mode}
  simpa only [zero_add, mul_zero, pow_zero, one_mul, Finset.sum_singleton] using estimate

theorem originalCore_lower {low high : ℕ} (ordered : low ≤ high) (field : ClosedJet 1) :
    ‖unitDiskCoreInto low field‖ ≤ apLoweringConstant low * ‖unitDiskCoreInto high field‖ := by
  rw [← unitLower_core ordered field]
  exact unitLower_bound ordered (unitDiskCoreInto high field)

def profileSourceConstant (grade : ℕ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∑ order ∈ Finset.range (grade + 1), polarOrderConstant order

theorem profileSourceConstant_nonnegative (grade : ℕ) : 0 ≤ profileSourceConstant grade := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun order _ => polarOrderConstant_nonnegative order)

theorem pureProfile_energy_source (grade order : ℕ) (paid : order ≤ grade)
    (field : ClosedJet 1) (mode : ℤ) :
    radialWithinEnergy (1 / 2) order (pureProfile mode field) ≤
      profileSourceConstant grade * ‖unitDiskCoreInto grade field‖ ^ 2 := by
  apply (pureProfile_energy_native grade order paid field mode (1 / 2) (by norm_num) (by norm_num)).trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum
    (fun other _ => polarOrderConstant_nonnegative other) (Finset.mem_range.mpr (by omega))) (by positivity)

def centerProfileBaseConstant (radius : ℝ) : ℝ :=
  profileSourceConstant 1 * (centerH1Constant radius * apLoweringConstant 3) ^ 2

theorem centerProfileBaseConstant_nonnegative (radius : ℝ) : 0 ≤ centerProfileBaseConstant radius :=
  mul_nonneg (profileSourceConstant_nonnegative 1) (sq_nonneg _)

theorem pinnedCenterProfile_base_energy (grade : ℕ) (large : 3 ≤ grade) (radius : ℝ)
    (mode : ℤ) (center : mode = 1 ∨ mode = -1) (frequency : ℝ) (bounded : |frequency| ≤ radius)
    (source : ClosedJet 1) (pure : angularClosedJet mode source = source) (order : ℕ) (small : order ≤ 1) :
    radialWithinEnergy (1 / 2) order (pureProfile mode (pinnedCenterSolution mode frequency source)) ≤
      centerProfileBaseConstant radius * ‖unitDiskCoreInto grade source‖ ^ 2 := by
  have initial := pureProfile_energy_source 1 order small (pinnedCenterSolution mode frequency source) mode
  have base := (pinnedCenterSolution_H1 radius mode center frequency bounded source pure).trans
    (mul_le_mul_of_nonneg_left (originalCore_lower large source) (centerH1Constant_nonnegative radius))
  have square := pow_le_pow_left₀ (norm_nonneg _) base 2
  exact initial.trans ((mul_le_mul_of_nonneg_left square (profileSourceConstant_nonnegative 1)).trans_eq (by
    unfold centerProfileBaseConstant
    ring))

/-- The source term in the exact ODE is the same original smooth datum.
Its sign and the factor 3 are kept literally. -/
theorem pinnedCenterProfile_energy_recurrence (radius : ℝ) (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (frequency : ℝ) (bounded : |frequency| ≤ radius) (source : ClosedJet 1)
    (pure : angularClosedJet mode source = source) (order : ℕ) :
    radialWithinEnergy (1 / 2) (order + 2) (pureProfile mode (pinnedCenterSolution mode frequency source)) ≤
      4 * (radialProductConstant (1 / 2) (by norm_num) (by norm_num) order *
        (∑ index ∈ Finset.range (order + 1), radialWithinEnergy (1 / 2) (order - index + 1)
          (pureProfile mode (pinnedCenterSolution mode frequency source))) +
        radialProductConstant (1 / 2) (by norm_num) (by norm_num) order *
        (∑ index ∈ Finset.range (order + 1), radialWithinEnergy (1 / 2) (order - index)
          (pureProfile mode (pinnedCenterSolution mode frequency source))) +
        (3 * radius ^ 2) ^ 2 * radialWithinEnergy (1 / 2) order
          (pureProfile mode (pinnedCenterSolution mode frequency source)) +
        radialWithinEnergy (1 / 2) order (pureProfile mode source)) :=
  centerODE_energy_recurrence (1 / 2) (by norm_num) (by norm_num) _ _
    (pureProfile_smooth mode _).contDiffOn (pureProfile_smooth mode source).contDiffOn
    (-3 * frequency ^ 2) (3 * radius ^ 2) (center_parameter_bound radius frequency bounded)
    (pureProfile_center_within_equation mode center frequency _ source
      (pinnedCenterSolution_pure mode center frequency source pure) pure
      (pinnedCenterSolution_equation mode center frequency source pure) (1 / 2) (by norm_num) (by norm_num)) order

end Grad.ActualCenterBounds
