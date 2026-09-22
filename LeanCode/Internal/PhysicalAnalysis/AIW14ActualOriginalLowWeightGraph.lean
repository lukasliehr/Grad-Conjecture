import AIW13OriginalLowWeightMultipliers

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularOriginalLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.PhaseAlgebra Grad.CircularHighRegularity
open Grad.AnnularCurrentGreen Grad.AnnularReconstruction Grad.GaugeCoefficients.Physical.WeightedTrace

theorem originalLowFromAJ_decode_coefficients (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (index : LowAnnularIndex) :
    lowStorageInverse lower positive * originalLowFromAJValueCurve parameters lower length positive lengthPositive index =
      originalLowInverseRatio parameters lower length positive lengthPositive index ∧
    lowMuCurve lower length positive index.2.val.2 * lowStorageInverse lower positive *
      originalLowFromAJCorrectionCurve parameters lower length positive lengthPositive index =
        originalLowInverseRatioSlope parameters lower length positive lengthPositive index ∧
    lowMuCurve lower length positive index.2.val.2 * lowStorageInverse lower positive *
      originalLowFromAJSlopeCurve parameters lower length positive lengthPositive index =
        cellFrequency index.2.val.2 • originalLowInverseRatio parameters lower length positive lengthPositive index := by
  constructor
  · apply ContinuousMap.ext
    intro radius
    change lowStorageInverse lower positive radius * (lowStorageWeight lower positive radius *
      originalLowInverseRatio parameters lower length positive lengthPositive index radius) = _
    calc
      _ = (lowStorageWeight lower positive radius * lowStorageInverse lower positive radius) *
        originalLowInverseRatio parameters lower length positive lengthPositive index radius := by ring
      _ = _ := by rw [lowStorage_inverse, one_mul]
  constructor
  · apply ContinuousMap.ext
    intro radius
    let m := lowMuCurve lower length positive index.2.val.2 radius
    let s := lowStorageWeight lower positive radius
    let t := lowStorageInverse lower positive radius
    let bd := originalLowInverseRatioSlope parameters lower length positive lengthPositive index radius
    have mu : m ≠ 0 := (lowMuCurve_pos lower length positive index.2.val.2 radius).ne'
    have storage : s * t = 1 := lowStorage_inverse lower positive radius
    change (m * t) * (s * m⁻¹ * bd) = bd
    calc
      _ = (m * m⁻¹) * (s * t) * bd := by ring
      _ = _ := by rw [mul_inv_cancel₀ mu, storage, one_mul, one_mul]
  · apply ContinuousMap.ext
    intro radius
    let m := lowMuCurve lower length positive index.2.val.2 radius
    let s := lowStorageWeight lower positive radius
    let t := lowStorageInverse lower positive radius
    let b := originalLowInverseRatio parameters lower length positive lengthPositive index radius
    let l := cellFrequency index.2.val.2
    have mu : m ≠ 0 := (lowMuCurve_pos lower length positive index.2.val.2 radius).ne'
    have storage : s * t = 1 := lowStorage_inverse lower positive radius
    change (m * t) * (l * (s * m⁻¹ * b)) = l * b
    calc
      _ = l * ((m * m⁻¹) * (s * t) * b) := by ring
      _ = _ := by rw [mul_inv_cancel₀ mu, storage, one_mul, one_mul]

theorem originalLowFromAJAmbient_value (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1)
    (field : LowEnergyAmbient lower) (index : LowAnnularIndex) :
    lowEnergyValue lower positive index
      (originalLowFromAJAmbient parameters lower length positive lengthPositive bounded field) =
      collarScalar 1 lower (originalLowInverseRatio parameters lower length positive lengthPositive index) (field 0 index) := by
  change collarScalar 1 lower (lowStorageInverse lower positive)
    (collarScalar 1 lower (originalLowFromAJValueCurve parameters lower length positive lengthPositive index) (field 0 index)) = _
  rw [collarScalar_mul_apply, (originalLowFromAJ_decode_coefficients parameters lower length positive lengthPositive index).1]

theorem originalLowFromAJAmbient_derivative (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1)
    (field : LowEnergyAmbient lower) (index : LowAnnularIndex) :
    lowEnergyDerivative lower length positive index
      (originalLowFromAJAmbient parameters lower length positive lengthPositive bounded field) =
      collarScalar 1 lower (originalLowInverseRatioSlope parameters lower length positive lengthPositive index) (field 0 index) +
        collarScalar 1 lower (originalLowInverseRatio parameters lower length positive lengthPositive index)
          ((cellFrequency index.2.val.2 : ℂ) • field 1 index) := by
  change collarScalar 1 lower (lowMuCurve lower length positive index.2.val.2)
    (collarScalar 1 lower (lowStorageInverse lower positive)
      (collarScalar 1 lower (originalLowFromAJCorrectionCurve parameters lower length positive lengthPositive index) (field 0 index) +
       collarScalar 1 lower (originalLowFromAJSlopeCurve parameters lower length positive lengthPositive index) (field 1 index))) = _
  rw [map_add, map_add, collarScalar_mul_apply, collarScalar_mul_apply,
    collarScalar_mul_apply, collarScalar_mul_apply,
    (originalLowFromAJ_decode_coefficients parameters lower length positive lengthPositive index).2.1,
    (originalLowFromAJ_decode_coefficients parameters lower length positive lengthPositive index).2.2,
    collarScalar_real_multiple, map_smul]
  rfl

def originalLowWeight (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (bounded : lower ≤ 1) :
    originalLowGraph lower →L[ℂ] lowEnergyGraph lower length positive :=
  ((originalLowFromAJAmbient parameters lower length positive lengthPositive bounded).comp
    (originalLowGraph lower).subtypeL).codRestrict (lowEnergyGraph lower length positive) (fun field => by
      intro index
      change CollarWeakDerivative lower
        (lowEnergyValue lower positive index (originalLowFromAJAmbient parameters lower length positive lengthPositive bounded field.val))
        (lowEnergyDerivative lower length positive index (originalLowFromAJAmbient parameters lower length positive lengthPositive bounded field.val))
      rw [originalLowFromAJAmbient_value, originalLowFromAJAmbient_derivative]
      exact collarWeakDerivative_scalar lower _ _
        (originalLowInverseRatio_hasDerivAt parameters lower length positive lengthPositive index)
        _ _ (field.property index))

end Grad.AnnularOriginalLow
