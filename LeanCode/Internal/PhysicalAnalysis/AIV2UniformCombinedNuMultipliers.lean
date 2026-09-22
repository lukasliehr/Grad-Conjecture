import AIV1OriginalHilbertNuGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularOriginalHigh
open Grad.ClosedJets Grad.AnnularVariational Grad.AnnularFluxTrace Grad.AnnularOmegaGraph
open Grad.AnnularHighTilt Grad.SourceCollarDivision

/-- Combined inverse coefficient r^alpha omega/nu, before taking any radius supremum. -/
def originalUnweightSlopeCurve (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) : C(ℝ, ℝ) :=
  highPowerCurve lower highTiltExponent positive * annularOmegaOverNuCurve lower length positive mode

/-- The actual radial product term (r^alpha)'/nu. -/
def originalUnweightValueSlopeCurve (lower : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) : C(ℝ, ℝ) :=
  ⟨fun radius => highPowerSlopeCurve lower highTiltExponent positive radius /
      Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2,
    (highPowerSlopeCurve lower highTiltExponent positive).continuous.div_const _⟩

theorem originalUnweightSlopeCurve_bound (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (mode : HighAnnularMode) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) :
    |originalUnweightSlopeCurve lower length positive mode radius| ≤ 1 + length⁻¹ := by
  have rp := positive.trans_le inside.1
  have np := Grad.AnnularFluxTrace.annularFrequency_pos mode
  have op := annularOmega_pos length radius rp mode
  have powerBound : radius ^ (highTiltExponent - 1) ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow rp.le inside.2
      (by norm_num [highTiltExponent] : 0 ≤ highTiltExponent - 1)
  change |highPowerCurve lower highTiltExponent positive radius *
    (annularOmegaCurve lower length positive mode radius /
      Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)| ≤ _
  rw [highPowerCurve_physical lower highTiltExponent positive radius inside,
    annularOmegaCurve_original lower length positive mode radius inside]
  change |radius ^ highTiltExponent * (annularOmega length radius mode /
    Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2)| ≤ _
  rw [abs_of_pos (mul_pos (Real.rpow_pos_of_pos rp _) (div_pos op np))]
  have ratio : annularOmega length radius mode /
      Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 ≤ (1 + length⁻¹) / radius :=
    (div_le_iff₀ np).mpr (annularOmega_le_nu length radius lengthPositive rp inside.2 mode)
  calc
    _ ≤ radius ^ highTiltExponent * ((1 + length⁻¹) / radius) :=
      mul_le_mul_of_nonneg_left ratio (Real.rpow_pos_of_pos rp _).le
    _ = (1 + length⁻¹) * radius ^ (highTiltExponent - 1) := by
      rw [Real.rpow_sub_one rp.ne']
      ring
    _ ≤ (1 + length⁻¹) * 1 := mul_le_mul_of_nonneg_left powerBound (by positivity)
    _ = _ := mul_one _

theorem originalUnweightValueSlopeCurve_bound (lower : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |originalUnweightValueSlopeCurve lower positive mode radius| ≤ highTiltExponent := by
  have rp := positive.trans_le inside.1
  have np := Grad.AnnularFluxTrace.annularFrequency_pos mode
  have frequencyOne : 1 ≤ Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 := by
    unfold Grad.AnnularVariational.annularFrequency
    linarith [abs_nonneg (mode.val.1 : ℝ), abs_nonneg (mode.val.2 : ℝ)]
  have powerBound : radius ^ (highTiltExponent - 1) ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow rp.le inside.2
      (by norm_num [highTiltExponent] : 0 ≤ highTiltExponent - 1)
  change |highPowerSlopeCurve lower highTiltExponent positive radius /
    Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2| ≤ _
  rw [highPowerSlopeCurve_physical lower highTiltExponent positive radius inside,
    abs_of_pos (div_pos (mul_pos highTiltExponent_pos (Real.rpow_pos_of_pos rp _)) np)]
  apply (div_le_iff₀ np).mpr
  exact (mul_le_mul_of_nonneg_left powerBound highTiltExponent_pos.le).trans
    (mul_le_mul_of_nonneg_left frequencyOne highTiltExponent_pos.le)

def originalUnweightSlope (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) : AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  annularScalarFamily lower (originalUnweightSlopeCurve lower length positive)
    (1 + length⁻¹) (by positivity) (originalUnweightSlopeCurve_bound lower length positive lengthPositive)

def originalUnweightValueSlope (lower : ℝ) (positive : 0 < lower) :
    AnnularBulk lower →L[ℂ] AnnularBulk lower :=
  annularScalarFamily lower (originalUnweightValueSlopeCurve lower positive)
    highTiltExponent highTiltExponent_pos.le (originalUnweightValueSlopeCurve_bound lower positive)

theorem originalUnweightSlope_bound (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (field : AnnularBulk lower) :
    ‖originalUnweightSlope lower length positive lengthPositive field‖ ≤ (1 + length⁻¹) * ‖field‖ :=
  annularScalarFamily_bound _ _ _ _ _ _

theorem originalUnweightValueSlope_bound (lower : ℝ) (positive : 0 < lower)
    (field : AnnularBulk lower) :
    ‖originalUnweightValueSlope lower positive field‖ ≤ highTiltExponent * ‖field‖ :=
  annularScalarFamily_bound _ _ _ _ _ _

end Grad.AnnularOriginalHigh
