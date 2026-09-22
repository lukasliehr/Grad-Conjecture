import AIW4ExactLowConjugationCurves

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators ENNReal
namespace Grad.AnnularOriginalLow
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularVariational
open Grad.CartesianState Grad.PhaseAlgebra

theorem originalLowRatio_first (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (mode : LowAnnularMode) (radius : ℝ) :
    originalLowRatio parameters lower length positive (0, mode) radius =
      originalLowScale parameters lower length mode / lowAmplitude length parameters.gamma mode *
        cellFrequency mode.val.2 / originalLowSmoothMu lower length positive mode.val.2 radius := by
  simp [originalLowRatio]

theorem originalLowRatio_second (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (mode : LowAnnularMode) :
    originalLowRatio parameters lower length positive (1, mode) = 1 := by
  simp [originalLowRatio]

theorem originalLowRatioSlope_first (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (mode : LowAnnularMode) (radius : ℝ) :
    originalLowRatioSlope parameters lower length positive (0, mode) radius =
      -(originalLowScale parameters lower length mode / lowAmplitude length parameters.gamma mode *
        cellFrequency mode.val.2) * originalLowSmoothMuSlope lower length positive mode.val.2 radius /
          originalLowSmoothMu lower length positive mode.val.2 radius ^ 2 := by
  have result := (hasDerivAt_const radius
    (originalLowScale parameters lower length mode / lowAmplitude length parameters.gamma mode *
      cellFrequency mode.val.2)).div
    (originalLowSmoothMu_hasDerivAt lower length positive mode.val.2 radius)
    (originalLowSmoothMu_pos lower length positive mode.val.2 radius).ne'
  have same : originalLowRatio parameters lower length positive (0, mode) =
      (fun point => originalLowScale parameters lower length mode / lowAmplitude length parameters.gamma mode *
        cellFrequency mode.val.2 / originalLowSmoothMu lower length positive mode.val.2 point) := by
    funext point
    exact originalLowRatio_first parameters lower length positive mode point
  change deriv (originalLowRatio parameters lower length positive (0, mode)) radius = _
  rw [same]
  have derivative := result.deriv
  change deriv (fun point => originalLowScale parameters lower length mode / lowAmplitude length parameters.gamma mode *
    cellFrequency mode.val.2 / originalLowSmoothMu lower length positive mode.val.2 point) radius = _ at derivative
  rw [derivative]
  ring

theorem originalLowRatioSlope_second (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (mode : LowAnnularMode) :
    originalLowRatioSlope parameters lower length positive (1, mode) = 0 := by
  apply ContinuousMap.ext
  intro radius
  change deriv (originalLowRatio parameters lower length positive (1, mode)) radius = 0
  rw [originalLowRatio_second]
  exact deriv_const _ _

/-- Six coefficients of the two triangular maps in the literal dr storage.
The derivative coordinate is obtained from w', not from differentiating q0. -/
def originalLowToAJValueCurve (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (index : LowAnnularIndex) : C(ℝ, ℝ) :=
  originalLowRatio parameters lower length positive index * lowStorageInverse lower positive

def originalLowToAJCorrectionCurve (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (index : LowAnnularIndex) : C(ℝ, ℝ) :=
  (cellFrequency index.2.val.2)⁻¹ •
    (originalLowRatioSlope parameters lower length positive index * lowStorageInverse lower positive)

def originalLowToAJSlopeCurve (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (index : LowAnnularIndex) : C(ℝ, ℝ) :=
  (cellFrequency index.2.val.2)⁻¹ •
    (originalLowRatio parameters lower length positive index *
      lowMuCurve lower length positive index.2.val.2 * lowStorageInverse lower positive)

def originalLowFromAJValueCurve (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (index : LowAnnularIndex) : C(ℝ, ℝ) :=
  lowStorageWeight lower positive * originalLowInverseRatio parameters lower length positive lengthPositive index

def originalLowFromAJCorrectionCurve (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (index : LowAnnularIndex) : C(ℝ, ℝ) :=
  lowStorageWeight lower positive *
    ⟨fun radius => (lowMuCurve lower length positive index.2.val.2 radius)⁻¹,
      (lowMuCurve lower length positive index.2.val.2).continuous.inv₀
        (fun radius => (lowMuCurve_pos lower length positive index.2.val.2 radius).ne')⟩ *
    originalLowInverseRatioSlope parameters lower length positive lengthPositive index

def originalLowFromAJSlopeCurve (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (index : LowAnnularIndex) : C(ℝ, ℝ) :=
  cellFrequency index.2.val.2 • (lowStorageWeight lower positive *
    ⟨fun radius => (lowMuCurve lower length positive index.2.val.2 radius)⁻¹,
      (lowMuCurve lower length positive index.2.val.2).continuous.inv₀
        (fun radius => (lowMuCurve_pos lower length positive index.2.val.2 radius).ne')⟩ *
    originalLowInverseRatio parameters lower length positive lengthPositive index)

theorem originalLowTriangular_inverse (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (index : LowAnnularIndex) (radius : ℝ) :
    originalLowFromAJValueCurve parameters lower length positive lengthPositive index radius *
      originalLowToAJValueCurve parameters lower length positive index radius = 1 ∧
    originalLowFromAJSlopeCurve parameters lower length positive lengthPositive index radius *
      originalLowToAJSlopeCurve parameters lower length positive index radius = 1 ∧
    originalLowFromAJCorrectionCurve parameters lower length positive lengthPositive index radius *
      originalLowToAJValueCurve parameters lower length positive index radius +
    originalLowFromAJSlopeCurve parameters lower length positive lengthPositive index radius *
      originalLowToAJCorrectionCurve parameters lower length positive index radius = 0 := by
  have storage := lowStorage_inverse lower positive radius
  have ratio := originalLowRatio_inverse parameters lower length positive lengthPositive index radius
  have slope := originalLowRatio_slope_cancel parameters lower length positive lengthPositive index radius
  have mu := (lowMuCurve_pos lower length positive index.2.val.2 radius).ne'
  have frequency := (cellFrequency_pos index.2.val.2).ne'
  let a := originalLowRatio parameters lower length positive index radius
  let ad := originalLowRatioSlope parameters lower length positive index radius
  let b := originalLowInverseRatio parameters lower length positive lengthPositive index radius
  let bd := originalLowInverseRatioSlope parameters lower length positive lengthPositive index radius
  let s := lowStorageWeight lower positive radius
  let t := lowStorageInverse lower positive radius
  let m := lowMuCurve lower length positive index.2.val.2 radius
  let l := cellFrequency index.2.val.2
  change (s * b) * (a * t) = 1 ∧
    (l * (s * m⁻¹ * b)) * (l⁻¹ * (a * m * t)) = 1 ∧
    (s * m⁻¹ * bd) * (a * t) + (l * (s * m⁻¹ * b)) * (l⁻¹ * (ad * t)) = 0
  change s * t = 1 at storage
  change b * a = 1 at ratio
  change bd * a + b * ad = 0 at slope
  change m ≠ 0 at mu
  change l ≠ 0 at frequency
  constructor
  · calc
      (s * b) * (a * t) = (s * t) * (b * a) := by ring
      _ = 1 := by rw [storage, ratio, one_mul]
  constructor
  · calc
      (l * (s * m⁻¹ * b)) * (l⁻¹ * (a * m * t)) =
        (l * l⁻¹) * (m⁻¹ * m) * (s * t) * (b * a) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ frequency, inv_mul_cancel₀ mu, storage, ratio]; ring
  · have cancel : (l * (s * m⁻¹ * b)) * (l⁻¹ * (ad * t)) = s * m⁻¹ * b * ad * t := by
      calc
        _ = (l * l⁻¹) * (s * m⁻¹ * b * ad * t) := by ring
        _ = _ := by rw [mul_inv_cancel₀ frequency, one_mul]
    rw [cancel]
    calc
      _ = s * t * m⁻¹ * (bd * a + b * ad) := by ring
      _ = 0 := by rw [slope, mul_zero]

end Grad.AnnularOriginalLow
