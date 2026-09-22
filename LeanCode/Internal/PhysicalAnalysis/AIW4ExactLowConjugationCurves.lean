import AIW3ActualSmoothLowFrequency
import AAX15InvertibleWeakConjugation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators ENNReal
namespace Grad.AnnularOriginalLow
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularVariational
open Grad.CartesianState Grad.PhaseAlgebra Grad.AnnularFourSource
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularSourceGraph
open Grad.CircularHighRegularity Grad.GaugeCoefficients.Physical.WeightedTrace

theorem originalLowRatio_positive (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (index : LowAnnularIndex) (radius : ℝ) :
    0 < originalLowRatio parameters lower length positive index radius := by
  unfold originalLowRatio
  split_ifs
  · change 0 < originalLowScale parameters lower length index.2 /
      lowAmplitude length parameters.gamma index.2 * cellFrequency index.2.val.2 /
        originalLowSmoothMu lower length positive index.2.val.2 radius
    exact div_pos (mul_pos (div_pos (originalLowScale_positive parameters lower length positive lengthPositive index.2)
      (lowAmplitude_pos length parameters.gamma index.2)) (cellFrequency_pos index.2.val.2))
      (originalLowSmoothMu_pos lower length positive index.2.val.2 radius)
  · exact zero_lt_one

def originalLowInverseRatio (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (index : LowAnnularIndex) : C(ℝ, ℝ) :=
  ⟨fun radius => (originalLowRatio parameters lower length positive index radius)⁻¹,
    (originalLowRatio parameters lower length positive index).continuous.inv₀
      (fun radius => (originalLowRatio_positive parameters lower length positive lengthPositive index radius).ne')⟩

theorem originalLowInverseRatio_smooth (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (index : LowAnnularIndex) :
    ContDiff ℝ ∞ (originalLowInverseRatio parameters lower length positive lengthPositive index) :=
  (originalLowRatio_smooth parameters lower length positive index).inv
    (fun radius => (originalLowRatio_positive parameters lower length positive lengthPositive index radius).ne')

def originalLowInverseRatioSlope (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (index : LowAnnularIndex) : C(ℝ, ℝ) :=
  ⟨deriv (originalLowInverseRatio parameters lower length positive lengthPositive index),
    (contDiff_infty_iff_deriv.mp
      (originalLowInverseRatio_smooth parameters lower length positive lengthPositive index)).2.continuous⟩

theorem originalLowInverseRatio_hasDerivAt (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (index : LowAnnularIndex) (radius : ℝ) :
    HasDerivAt (originalLowInverseRatio parameters lower length positive lengthPositive index)
      (originalLowInverseRatioSlope parameters lower length positive lengthPositive index radius) radius :=
  (originalLowInverseRatio_smooth parameters lower length positive lengthPositive index).differentiable
    (by simp) radius |>.hasDerivAt

theorem originalLowRatio_inverse (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (index : LowAnnularIndex) (radius : ℝ) :
    originalLowInverseRatio parameters lower length positive lengthPositive index radius *
      originalLowRatio parameters lower length positive index radius = 1 :=
  inv_mul_cancel₀ (originalLowRatio_positive parameters lower length positive lengthPositive index radius).ne'

theorem originalLowRatio_slope_cancel (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (index : LowAnnularIndex) (radius : ℝ) :
    originalLowInverseRatioSlope parameters lower length positive lengthPositive index radius *
      originalLowRatio parameters lower length positive index radius +
    originalLowInverseRatio parameters lower length positive lengthPositive index radius *
      originalLowRatioSlope parameters lower length positive index radius = 0 := by
  have result := (originalLowInverseRatio_hasDerivAt parameters lower length positive lengthPositive index radius).mul
    (originalLowRatio_hasDerivAt parameters lower length positive index radius)
  have constant : HasDerivAt
      (fun point => originalLowInverseRatio parameters lower length positive lengthPositive index point *
        originalLowRatio parameters lower length positive index point) 0 radius := by
    apply (hasDerivAt_const radius (1 : ℝ)).congr_of_eventuallyEq
    filter_upwards [] with point
    exact originalLowRatio_inverse parameters lower length positive lengthPositive index point
  exact result.unique constant

/-- Actual reversible product rule for v = S_ell Lambda (a_m mu)^-1 w.
Here w and d are the decoded ADY value and genuine derivative. -/
theorem originalLowRatio_weak_iff (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (index : LowAnnularIndex)
    (w d : CollarL2 (ComplexEuclidean 1) lower) :
    Grad.GaugeCoefficients.Physical.WeightedTrace.CollarWeakDerivative lower
      (collarScalar 1 lower (originalLowRatio parameters lower length positive index) w)
      (collarScalar 1 lower (originalLowRatioSlope parameters lower length positive index) w +
        collarScalar 1 lower (originalLowRatio parameters lower length positive index) d) ↔
      Grad.GaugeCoefficients.Physical.WeightedTrace.CollarWeakDerivative lower w d :=
  collarWeakDerivative_conjugation lower _ _ _ _
    (originalLowRatio_hasDerivAt parameters lower length positive index)
    (originalLowInverseRatio_hasDerivAt parameters lower length positive lengthPositive index)
    (originalLowRatio_inverse parameters lower length positive lengthPositive index)
    (originalLowRatio_slope_cancel parameters lower length positive lengthPositive index) w d

end Grad.AnnularOriginalLow
