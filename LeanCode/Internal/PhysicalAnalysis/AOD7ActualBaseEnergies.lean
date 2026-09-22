import AOD6FiniteRadialInduction
import ARS2LiteralRadialSource

noncomputable section
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped ContDiff BigOperators Interval
namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.AnnularSourceGraph Grad.SourceCollarDivision

def actualRadialJetEnergy (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : highDiskL2) (radial : ℕ) (mode : ℤ) : ℝ :=
  radialWithinEnergy lower radial (actualRadialValue lower positive bounded mode parameter source)

theorem actualRadialJetEnergy_nonnegative (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : highDiskL2) (radial : ℕ) (mode : ℤ) :
    0 ≤ actualRadialJetEnergy lower positive bounded parameter source radial mode :=
  radialWithinEnergy_nonnegative lower positive.le bounded.le radial _

theorem actualRadialJetEnergy_zero (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : highDiskL2) (mode : ℤ) :
    actualRadialJetEnergy lower positive bounded parameter source 0 mode =
      ‖diskL2Radial lower positive bounded.le mode (highDiskBulk (highRobinWeakInverse parameter source))‖ ^ 2 := by
  simpa only [actualRadialJetEnergy, radialWithinEnergy, iteratedDerivWithin_zero] using
    actualRadialValue_energy lower positive bounded mode parameter source

theorem actualRadialJetEnergy_one (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : highDiskL2) (mode : ℤ) :
    actualRadialJetEnergy lower positive bounded parameter source 1 mode =
      ‖weightedRadialCoordinate 1 lower 1
        (diskRadial lower positive bounded.le mode (highRobinWeakInverse parameter source).val)‖ ^ 2 := by
  have literal : actualRadialJetEnergy lower positive bounded parameter source 1 mode =
      ∫ radius in lower..1, radius * ‖actualRadialSlope lower positive bounded mode parameter source radius‖ ^ 2 := by
    unfold actualRadialJetEnergy radialWithinEnergy
    rw [iteratedDerivWithin_one]
    apply intervalIntegral.integral_congr
    intro radius member
    have inside : radius ∈ Icc lower 1 := by simpa only [uIcc_of_le bounded.le] using member
    dsimp only
    rw [actualRadialSlope_eq_deriv lower positive bounded mode parameter source radius inside]
  exact literal.trans (actualRadialSlope_energy lower positive bounded mode parameter source)

theorem actualRadialJetEnergy_two (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core)
    (mode : ℤ) (high : mode ∉ lowAngularModes) :
    actualRadialJetEnergy lower positive bounded parameter source 2 mode =
      actualSecondRadialEnergy lower positive bounded parameter source core mode := by
  have literal := (actualSecondRadialEnergy_literal lower positive bounded parameter source core same mode high).symm
  simpa only [actualRadialJetEnergy, radialWithinEnergy, show (2 : ℕ) = 1 + 1 from rfl,
    iteratedDerivWithin_succ, iteratedDerivWithin_one, iteratedDerivWithin_zero] using literal

private theorem weightedSecondRadialConstant_ceiling (lower parameter ceiling : ℝ) (grade : ℕ)
    (parameterBound : |parameter| ≤ ceiling) :
    weightedSecondRadialConstant lower parameter grade ≤ weightedSecondRadialConstant lower ceiling grade := by
  have even : |parameter| ^ 4 = parameter ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 by omega, pow_mul, sq_abs, ← pow_mul]
  have fourth : parameter ^ 4 ≤ ceiling ^ 4 := by
    simpa only [even] using pow_le_pow_left₀ (abs_nonneg parameter) parameterBound 4
  have factor : secondRadialFactor lower parameter ≤ secondRadialFactor lower ceiling :=
    add_le_add le_rfl fourth
  exact mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_right factor (zeroOneCollarConstant_nonnegative grade)) le_rfl) (by norm_num : (0 : ℝ) ≤ 4)

/-- Exact finite base counts0,1,2 with the literal ordinary smooth source norm. -/
theorem actualRadial_base_finite (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (ceiling parameter : ℝ) (parameterBound : |parameter| ≤ ceiling) (grade : ℕ)
    (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core)
    (radial : ℕ) (small : radial ≤ 2) (modes : Finset ℤ) (highModes : ∀ mode ∈ modes, mode ∉ lowAngularModes) :
    (∑ mode ∈ modes, mixedRadialEnergy grade radial (actualRadialJetEnergy lower positive bounded parameter source) mode) ≤
      (zeroOneCollarConstant grade + weightedSecondRadialConstant lower ceiling grade) * ‖unitDiskCoreInto grade core‖ ^ 2 := by
  let completed := unitDiskCoreInto grade core
  have highCompleted : unitDiskBulk grade completed ∈ highDiskL2 := by
    rw [unitDiskBulk_core, ← same]
    exact source.property
  have sourceEquality : (⟨unitDiskBulk grade completed, highCompleted⟩ : highDiskL2) = source :=
    Subtype.ext ((unitDiskBulk_core grade core).trans same.symm)
  have zeroOne : (∑ mode ∈ modes, inverseZeroOneEnergy lower positive bounded.le parameter grade source mode) ≤
      zeroOneCollarConstant grade * ‖completed‖ ^ 2 :=
    (congrArg (fun current : highDiskL2 =>
      ∑ mode ∈ modes, inverseZeroOneEnergy lower positive bounded.le parameter grade current mode) sourceEquality).symm.trans_le
      (weakInverse_zeroOne_finite lower positive bounded.le parameter grade completed highCompleted modes)
  have secondBound : (∑ mode ∈ modes, |(mode : ℝ)| ^ (2 * grade) *
      actualSecondRadialEnergy lower positive bounded parameter source core mode) ≤
      weightedSecondRadialConstant lower ceiling grade * ‖completed‖ ^ 2 := by
    have base := actualSecondRadial_weighted_finite lower positive bounded parameter grade completed highCompleted core
      (unitDiskBulk_core grade core) modes highModes
    have transfer := congrArg (fun current : highDiskL2 => ∑ mode ∈ modes, |(mode : ℝ)| ^ (2 * grade) *
      actualSecondRadialEnergy lower positive bounded parameter current core mode) sourceEquality
    exact (transfer.symm.trans_le base).trans (mul_le_mul_of_nonneg_right
      (weightedSecondRadialConstant_ceiling lower parameter ceiling grade parameterBound) (sq_nonneg _))
  have zeroOneEnlarge : zeroOneCollarConstant grade * ‖completed‖ ^ 2 ≤
      (zeroOneCollarConstant grade + weightedSecondRadialConstant lower ceiling grade) * ‖completed‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (weightedSecondRadialConstant_nonnegative lower ceiling grade)) (sq_nonneg _)
  have secondEnlarge : weightedSecondRadialConstant lower ceiling grade * ‖completed‖ ^ 2 ≤
      (zeroOneCollarConstant grade + weightedSecondRadialConstant lower ceiling grade) * ‖completed‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (zeroOneCollarConstant_nonnegative grade)) (sq_nonneg _)
  interval_cases radial
  · apply (Finset.sum_le_sum (fun mode _ => ?_)).trans (zeroOne.trans zeroOneEnlarge)
    rw [mixedRadialEnergy, Nat.sub_zero, actualRadialJetEnergy_zero]
    exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg (abs_nonneg _) _) (sq_nonneg _))
  · apply (Finset.sum_le_sum (fun mode _ => ?_)).trans (zeroOne.trans zeroOneEnlarge)
    rw [mixedRadialEnergy, show grade + 2 - 1 = grade + 1 by omega, actualRadialJetEnergy_one]
    exact le_add_of_nonneg_left (mul_nonneg (pow_nonneg (abs_nonneg _) _) (sq_nonneg _))
  · have equal : (∑ mode ∈ modes, mixedRadialEnergy grade 2
        (actualRadialJetEnergy lower positive bounded parameter source) mode) =
        ∑ mode ∈ modes, |(mode : ℝ)| ^ (2 * grade) * actualSecondRadialEnergy lower positive bounded parameter source core mode := by
      apply Finset.sum_congr rfl
      intro mode member
      rw [mixedRadialEnergy, show grade + 2 - 2 = grade by omega,
        actualRadialJetEnergy_two lower positive bounded parameter source core same mode (highModes mode member)]
    exact equal.trans_le (secondBound.trans secondEnlarge)

end Grad.CircularHighRegularity
