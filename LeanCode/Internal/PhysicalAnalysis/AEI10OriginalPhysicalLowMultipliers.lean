import AEI9LiteralLowSevenComponentIdentity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Ledger

theorem lowInputRadiusCurve_actual (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (mode : LowAnnularMode) (radius : ℝ) (inside : lower ≤ radius) :
    lowInputRadiusCurve parameters lower length positive mode radius =
      radius⁻¹ / (lowAmplitude length parameters.gamma mode * lowMu length radius mode.val.2) := by
  change (lowAmplitude length parameters.gamma mode)⁻¹ * lowRadiusMuRatio lower length positive mode.val.2 radius = _
  rw [lowRadiusMuRatio_actual lower length positive mode.val.2 radius inside]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem lowInputCellCurve_actual (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (mode : LowAnnularMode) (radius : ℝ) (inside : lower ≤ radius) :
    lowInputCellCurve parameters lower length positive mode radius =
      (mode.val.2 : ℝ) / (lowAmplitude length parameters.gamma mode * lowMu length radius mode.val.2) := by
  change (length * (lowAmplitude length parameters.gamma mode)⁻¹) * lowCellMuRatio lower length positive mode.val.2 radius = _
  rw [lowCellMuRatio_actual lower length positive mode.val.2 radius inside]
  have mu := (lowMu_pos length radius mode.val.2 (positive.trans_le inside)).ne'
  have amplitude := (lowAmplitude_pos length parameters.gamma mode).ne'
  field_simp [lengthPositive.ne']

theorem lowInputAngularCurve_actual (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (mode : LowAnnularMode) (radius : ℝ) (inside : lower ≤ radius) :
    lowInputAngularCurve parameters lower length positive mode radius =
      ((mode.val.1 : ℝ) / radius) / (lowAmplitude length parameters.gamma mode * lowMu length radius mode.val.2) := by
  change (mode.val.1 : ℝ) * lowInputRadiusCurve parameters lower length positive mode radius = _
  rw [lowInputRadiusCurve_actual parameters lower length positive mode radius inside]
  simp only [div_eq_mul_inv]
  ring

theorem lowInputRadiusCurve_decode (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (mode : LowAnnularMode) (radius : ℝ) (inside : lower ≤ radius) :
    lowInputRadiusCurve parameters lower length positive mode radius *
      (lowAmplitude length parameters.gamma mode * lowMu length radius mode.val.2) = radius⁻¹ := by
  rw [lowInputRadiusCurve_actual parameters lower length positive mode radius inside]
  exact div_mul_cancel₀ _ (mul_ne_zero (lowAmplitude_pos length parameters.gamma mode).ne'
    (lowMu_pos length radius mode.val.2 (positive.trans_le inside)).ne')

theorem lowInputCellCurve_decode (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (mode : LowAnnularMode) (radius : ℝ) (inside : lower ≤ radius) :
    lowInputCellCurve parameters lower length positive mode radius *
      (lowAmplitude length parameters.gamma mode * lowMu length radius mode.val.2) = (mode.val.2 : ℝ) := by
  rw [lowInputCellCurve_actual parameters lower length lengthPositive positive mode radius inside]
  exact div_mul_cancel₀ _ (mul_ne_zero (lowAmplitude_pos length parameters.gamma mode).ne'
    (lowMu_pos length radius mode.val.2 (positive.trans_le inside)).ne')

theorem lowInputAngularCurve_decode (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (mode : LowAnnularMode) (radius : ℝ) (inside : lower ≤ radius) :
    lowInputAngularCurve parameters lower length positive mode radius *
      (lowAmplitude length parameters.gamma mode * lowMu length radius mode.val.2) = (mode.val.1 : ℝ) / radius := by
  rw [lowInputAngularCurve_actual parameters lower length positive mode radius inside]
  exact div_mul_cancel₀ _ (mul_ne_zero (lowAmplitude_pos length parameters.gamma mode).ne'
    (lowMu_pos length radius mode.val.2 (positive.trans_le inside)).ne')

end Grad.AnnularCurrentLow
