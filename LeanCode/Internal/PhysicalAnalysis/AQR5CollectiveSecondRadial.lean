import AQR4SecondRadialIntegral
import ANQ8ActualZeroOneCollarConsumer

noncomputable section
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.AnnularSourceGraph Grad.SourceCollarDivision Grad.SourceBoundaryTrace

local instance aqrUnitNormedSpace0 : NormedSpace ℂ (unitDiskSobolev 0) :=
  (unitDiskSobolev 0).normedSpace

def secondRadialFactor (lower parameter : ℝ) : ℝ :=
  (lower⁻¹) ^ 2 + (lower⁻¹) ^ 4 + parameter ^ 4

theorem secondRadialFactor_nonnegative (lower parameter : ℝ) : 0 ≤ secondRadialFactor lower parameter := by
  unfold secondRadialFactor
  positivity

private theorem weightedSecond_domination (a b c v s m n : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hv : 0 ≤ v) (hs : 0 ≤ s)
    (hm : 1 ≤ m) (hn : 1 ≤ n) :
    a * s + (m * b + c) * v ≤ (a + b + c) * (m * v + n * s) := by
  have sv : s ≤ n * s := by nlinarith
  have vv : v ≤ m * v := by nlinarith
  have first := mul_le_mul_of_nonneg_left sv ha
  have second := mul_le_mul_of_nonneg_left vv hc
  have cross1 := mul_nonneg ha (mul_nonneg (by linarith : 0 ≤ m) hv)
  have cross2 := mul_nonneg (hb.trans (le_add_of_nonneg_right hc)) (mul_nonneg (by linarith : 0 ≤ n) hs)
  nlinarith

theorem actualSecondRadialEnergy_zeroOne (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : highDiskL2) (core : ClosedJet 1) (same : source.val = closedL2Core core)
    (mode : ℤ) (high : mode ∉ lowAngularModes) :
    actualSecondRadialEnergy lower positive bounded parameter source core mode ≤
      4 * (secondRadialFactor lower parameter * inverseZeroOneEnergy lower positive bounded.le parameter 0 source mode +
        ‖diskL2Radial lower positive bounded.le mode source.val‖ ^ 2) := by
  let valueEnergy : ℝ := ‖diskL2Radial lower positive bounded.le mode
    (highDiskBulk (highRobinWeakInverse parameter source))‖ ^ 2
  let slopeEnergy : ℝ := ‖weightedRadialCoordinate 1 lower 1
    (diskRadial lower positive bounded.le mode (highRobinWeakInverse parameter source).val)‖ ^ 2
  let forcingEnergy : ℝ := ‖diskL2Radial lower positive bounded.le mode source.val‖ ^ 2
  have second : actualSecondRadialEnergy lower positive bounded parameter source core mode ≤
      4 * ((lower⁻¹) ^ 2 * slopeEnergy +
        ((mode : ℝ) ^ 4 * (lower⁻¹) ^ 4 + parameter ^ 4) * valueEnergy + forcingEnergy) :=
    actualSecondRadialEnergy_bound lower positive bounded parameter source core same mode
  have mode2 : (1 : ℝ) ≤ |(mode : ℝ)| ^ 2 := (by norm_num : (1 : ℝ) ≤ 9).trans (highMode_sq mode high)
  have mode4 : (1 : ℝ) ≤ |(mode : ℝ)| ^ 4 := by nlinarith [sq_nonneg (|(mode : ℝ)| ^ 2 - 1)]
  have weighted : (lower⁻¹) ^ 2 * slopeEnergy +
      (|(mode : ℝ)| ^ 4 * (lower⁻¹) ^ 4 + parameter ^ 4) * valueEnergy ≤
      secondRadialFactor lower parameter * (|(mode : ℝ)| ^ 4 * valueEnergy + |(mode : ℝ)| ^ 2 * slopeEnergy) :=
    weightedSecond_domination ((lower⁻¹) ^ 2) ((lower⁻¹) ^ 4) (parameter ^ 4)
      valueEnergy slopeEnergy (|(mode : ℝ)| ^ 4) (|(mode : ℝ)| ^ 2)
      (by positivity) (by positivity) (by positivity) (sq_nonneg _) (sq_nonneg _) mode4 mode2
  have even : |(mode : ℝ)| ^ 4 = (mode : ℝ) ^ 4 := by
    calc
      _ = (|(mode : ℝ)| ^ 2) ^ 2 := by ring
      _ = ((mode : ℝ) ^ 2) ^ 2 := by rw [sq_abs]
      _ = _ := by ring
  have weightedActual : (lower⁻¹) ^ 2 * slopeEnergy +
      ((mode : ℝ) ^ 4 * (lower⁻¹) ^ 4 + parameter ^ 4) * valueEnergy ≤
      secondRadialFactor lower parameter * (|(mode : ℝ)| ^ 4 * valueEnergy + |(mode : ℝ)| ^ 2 * slopeEnergy) :=
    (congrArg (fun frequency : ℝ => (lower⁻¹) ^ 2 * slopeEnergy +
      (frequency * (lower⁻¹) ^ 4 + parameter ^ 4) * valueEnergy) even).symm.le.trans weighted
  have zeroOne : |(mode : ℝ)| ^ 4 * valueEnergy + |(mode : ℝ)| ^ 2 * slopeEnergy =
      inverseZeroOneEnergy lower positive bounded.le parameter 0 source mode := rfl
  have bound : actualSecondRadialEnergy lower positive bounded parameter source core mode ≤
      4 * (secondRadialFactor lower parameter *
        (|(mode : ℝ)| ^ 4 * valueEnergy + |(mode : ℝ)| ^ 2 * slopeEnergy) + forcingEnergy) :=
    second.trans (mul_le_mul_of_nonneg_left (add_le_add weightedActual (le_refl forcingEnergy))
      (by norm_num : (0 : ℝ) ≤ 4))
  exact bound.trans_eq (congrArg (fun energy : ℝ =>
    4 * (secondRadialFactor lower parameter * energy + forcingEnergy)) zeroOne)

def secondRadialSourceConstant (lower parameter : ℝ) : ℝ :=
  4 * (secondRadialFactor lower parameter * zeroOneCollarConstant 0 +
    diskRadialL2Bound ^ 2 * ‖unitDiskBulk 0‖ ^ 2)

private theorem finite_second_energy_bound (modes : Finset ℤ) (energy zeroOne forcing : ℤ → ℝ)
    (factor zeroConstant radial bulk size : ℝ) (factorNonnegative : 0 ≤ factor)
    (pointwise : ∀ mode ∈ modes, energy mode ≤ 4 * (factor * zeroOne mode + forcing mode))
    (zeroBound : (∑ mode ∈ modes, zeroOne mode) ≤ zeroConstant * size ^ 2)
    (forceBound : (∑ mode ∈ modes, forcing mode) ≤ radial ^ 2 * (bulk * size) ^ 2) :
    (∑ mode ∈ modes, energy mode) ≤ 4 * (factor * zeroConstant + radial ^ 2 * bulk ^ 2) * size ^ 2 := by
  have pointwiseSum := Finset.sum_le_sum pointwise
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum] at pointwiseSum
  exact pointwiseSum.trans ((mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left zeroBound factorNonnegative) forceBound)
    (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by ring))

private theorem operator_bound_sq {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F] (mapping : E →L[ℂ] F) (field : E) :
    ‖mapping field‖ ^ 2 ≤ (‖mapping‖ * ‖field‖) ^ 2 :=
  pow_le_pow_left₀ (norm_nonneg _) (mapping.le_opNorm field) 2

theorem actualSecondRadial_finite (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : unitDiskSobolev 0) (high : unitDiskBulk 0 source ∈ highDiskL2)
    (core : ClosedJet 1) (same : unitDiskBulk 0 source = closedL2Core core)
    (modes : Finset ℤ) (highModes : ∀ mode ∈ modes, mode ∉ lowAngularModes) :
    (∑ mode ∈ modes, actualSecondRadialEnergy lower positive bounded parameter
      ⟨unitDiskBulk 0 source, high⟩ core mode) ≤ secondRadialSourceConstant lower parameter * ‖source‖ ^ 2 := by
  let forcingEnergy : ℤ → ℝ := fun mode => ‖diskL2Radial lower positive bounded.le mode (unitDiskBulk 0 source)‖ ^ 2
  have forcing : (∑ mode ∈ modes, forcingEnergy mode) ≤ diskRadialL2Bound ^ 2 * ‖unitDiskBulk 0 source‖ ^ 2 :=
    diskL2Radial_finite_energy lower positive bounded.le (unitDiskBulk 0 source) modes
  have bulk : ‖unitDiskBulk 0 source‖ ^ 2 ≤ (‖unitDiskBulk 0‖ * ‖source‖) ^ 2 :=
    @operator_bound_sq (unitDiskSobolev 0) (DiskL2 1) inferInstance inferInstance
      aqrUnitNormedSpace0 inferInstance (unitDiskBulk 0) source
  have forceBound : (∑ mode ∈ modes, forcingEnergy mode) ≤ diskRadialL2Bound ^ 2 * (‖unitDiskBulk 0‖ * ‖source‖) ^ 2 :=
    forcing.trans (mul_le_mul_of_nonneg_left bulk (sq_nonneg diskRadialL2Bound))
  exact finite_second_energy_bound modes
    (actualSecondRadialEnergy lower positive bounded parameter ⟨unitDiskBulk 0 source, high⟩ core)
    (inverseZeroOneEnergy lower positive bounded.le parameter 0 ⟨unitDiskBulk 0 source, high⟩)
    forcingEnergy (secondRadialFactor lower parameter) (zeroOneCollarConstant 0)
    diskRadialL2Bound ‖unitDiskBulk 0‖ ‖source‖ (secondRadialFactor_nonnegative lower parameter)
    (fun mode member => actualSecondRadialEnergy_zeroOne lower positive bounded parameter
      ⟨unitDiskBulk 0 source, high⟩ core same mode (highModes mode member))
    (weakInverse_zeroOne_finite lower positive bounded.le parameter 0 source high modes) forceBound

end Grad.CircularHighRegularity
