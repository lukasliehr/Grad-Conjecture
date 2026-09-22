import AIW12UniformFromAJCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularOriginalLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.PhaseAlgebra Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem originalLowFromAJ_curves_bound (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1)
    (index : LowAnnularIndex) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |originalLowFromAJValueCurve parameters lower length positive lengthPositive index radius| ≤
      originalLowFromAJConstant parameters length * lower ^ (-(15 / 4 : ℝ)) ∧
    |originalLowFromAJCorrectionCurve parameters lower length positive lengthPositive index radius| ≤
      originalLowFromAJConstant parameters length * lower ^ (-(15 / 4 : ℝ)) ∧
    |originalLowFromAJSlopeCurve parameters lower length positive lengthPositive index radius| ≤
      originalLowFromAJConstant parameters length * lower ^ (-(15 / 4 : ℝ)) := by
  have factors := originalLowFromAJ_factors_bound parameters lower length positive lengthPositive bounded index radius inside
  have storage := originalLow_storage_bounds lower radius positive inside
  have frequency := cellFrequency_pos index.2.val.2
  have muPositive := lowMu_pos length radius index.2.val.2 (positive.trans_le inside.1)
  have physical : lowMuCurve lower length positive index.2.val.2 radius = lowMu length radius index.2.val.2 := by
    change lowMu length (max lower radius) index.2.val.2 = _
    rw [max_eq_right inside.1]
  have constantNonnegative : 0 ≤ originalLowFromAJConstant parameters length :=
    zero_le_one.trans (originalLowFromAJConstant_dominates parameters length lengthPositive).2.2.2
  have weighted (value : ℝ) (nonnegative : 0 ≤ value)
      (estimate : value ≤ originalLowFromAJConstant parameters length * lower⁻¹) :
      lowStorageWeight lower positive radius * value ≤ originalLowFromAJConstant parameters length * lower ^ (-(15 / 4 : ℝ)) := by
    have compared := mul_le_mul storage.2.2.2 estimate nonnegative (Real.rpow_pos_of_pos positive _).le
    have power := mul_le_mul_of_nonneg_left (originalLowFromAJ_storage_power lower positive bounded) constantNonnegative
    calc
      _ ≤ lower ^ (-(7 / 4 : ℝ)) * (originalLowFromAJConstant parameters length * lower⁻¹) := compared
      _ = originalLowFromAJConstant parameters length * (lower⁻¹ * lower ^ (-(7 / 4 : ℝ))) := by ring
      _ ≤ _ := power
  constructor
  · change |lowStorageWeight lower positive radius *
      originalLowInverseRatio parameters lower length positive lengthPositive index radius| ≤ _
    rw [abs_mul, abs_of_pos storage.2.2.1]
    exact weighted _ (abs_nonneg _) factors.1
  constructor
  · change |lowStorageWeight lower positive radius * (lowMuCurve lower length positive index.2.val.2 radius)⁻¹ *
      originalLowInverseRatioSlope parameters lower length positive lengthPositive index radius| ≤ _
    rw [physical, abs_mul, abs_mul, abs_of_pos storage.2.2.1, abs_of_pos (inv_pos.mpr muPositive)]
    have equality : lowStorageWeight lower positive radius * (lowMu length radius index.2.val.2)⁻¹ *
        |originalLowInverseRatioSlope parameters lower length positive lengthPositive index radius| =
      lowStorageWeight lower positive radius *
        (|originalLowInverseRatioSlope parameters lower length positive lengthPositive index radius| / lowMu length radius index.2.val.2) := by ring
    rw [equality]
    exact weighted _ (div_nonneg (abs_nonneg _) muPositive.le) factors.2.1
  · change |cellFrequency index.2.val.2 * (lowStorageWeight lower positive radius *
      (lowMuCurve lower length positive index.2.val.2 radius)⁻¹ *
        originalLowInverseRatio parameters lower length positive lengthPositive index radius)| ≤ _
    rw [physical, abs_mul, abs_mul, abs_mul, abs_of_pos frequency,
      abs_of_pos storage.2.2.1, abs_of_pos (inv_pos.mpr muPositive)]
    have equality : cellFrequency index.2.val.2 * (lowStorageWeight lower positive radius *
        (lowMu length radius index.2.val.2)⁻¹ * |originalLowInverseRatio parameters lower length positive lengthPositive index radius|) =
      lowStorageWeight lower positive radius * (cellFrequency index.2.val.2 *
        |originalLowInverseRatio parameters lower length positive lengthPositive index radius| / lowMu length radius index.2.val.2) := by ring
    rw [equality]
    exact weighted _ (div_nonneg (mul_nonneg frequency.le (abs_nonneg _)) muPositive.le) factors.2.2

def originalLowFromAJBulkMap (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1) (slot : Fin 3) :
    LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower :=
  originalLowScalarFamily lower
    (fun index => ![originalLowFromAJValueCurve parameters lower length positive lengthPositive index,
      originalLowFromAJCorrectionCurve parameters lower length positive lengthPositive index,
      originalLowFromAJSlopeCurve parameters lower length positive lengthPositive index] slot)
    (originalLowFromAJConstant parameters length * lower ^ (-(15 / 4 : ℝ)))
    (mul_nonneg (zero_le_one.trans (originalLowFromAJConstant_dominates parameters length lengthPositive).2.2.2)
      (Real.rpow_pos_of_pos positive _).le)
    (fun index radius inside => by
      have bounds := originalLowFromAJ_curves_bound parameters lower length positive lengthPositive bounded index radius inside
      fin_cases slot
      · exact bounds.1
      · exact bounds.2.1
      · exact bounds.2.2)

def originalLowFromAJAmbient (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1) :
    LowEnergyAmbient lower →L[ℂ] LowEnergyAmbient lower :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => LowEnergyBulk lower)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![
      (originalLowFromAJBulkMap parameters lower length positive lengthPositive bounded 0).comp (PiLp.proj 2 _ 0),
      (originalLowFromAJBulkMap parameters lower length positive lengthPositive bounded 1).comp (PiLp.proj 2 _ 0) +
        (originalLowFromAJBulkMap parameters lower length positive lengthPositive bounded 2).comp (PiLp.proj 2 _ 1)])

end Grad.AnnularOriginalLow
