import AEC9NormalizedDerivativeEnergyBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators
namespace Grad.AnnularLowVolterra
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularVariational Grad.CartesianState

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def lowDerivativeDensity (parameters : PhaseParameters) (length radius : ℝ) (mode : LowAnnularMode)
    (first second forcingFirst forcingSecond : E) : ℝ :=
  radius ^ (-(7 / 2 : ℝ)) *
    (‖(lowMu length radius mode.val.2)⁻¹ •
      (lowReferenceFirst parameters length radius mode first second + lowMu length radius mode.val.2 • forcingFirst)‖ ^ 2 +
     ‖(lowMu length radius mode.val.2)⁻¹ •
      (lowReferenceSecond parameters length radius mode first second + lowMu length radius mode.val.2 • forcingSecond)‖ ^ 2)

theorem lowDerivativeDensity_continuousAt (parameters : PhaseParameters) (length radius : ℝ)
    (mode : LowAnnularMode) (positive : 0 < radius)
    (first second forcingFirst forcingSecond : ℝ → E)
    (firstContinuous : ContinuousAt first radius) (secondContinuous : ContinuousAt second radius)
    (forceFirstContinuous : ContinuousAt forcingFirst radius) (forceSecondContinuous : ContinuousAt forcingSecond radius) :
    ContinuousAt (fun point => lowDerivativeDensity parameters length point mode
      (first point) (second point) (forcingFirst point) (forcingSecond point)) radius := by
  have muContinuous := (lowMu_hasDerivAt length radius mode.val.2 positive).continuousAt
  have inverseContinuous := (lowMuInverse_hasDerivAt length radius mode.val.2 positive).continuousAt
  have firstRow := ((lowReferenceEntry_continuousAt parameters length radius mode positive 0 0).smul firstContinuous).add
    ((lowReferenceEntry_continuousAt parameters length radius mode positive 0 1).smul secondContinuous)
  have secondRow := ((lowReferenceEntry_continuousAt parameters length radius mode positive 1 0).smul firstContinuous).add
    ((lowReferenceEntry_continuousAt parameters length radius mode positive 1 1).smul secondContinuous)
  simp only [lowDerivativeDensity, lowReferenceFirst_matrix, lowReferenceSecond_matrix]
  exact (Real.hasDerivAt_rpow_const (x := radius) (p := -(7 / 2 : ℝ)) (Or.inl positive.ne')).continuousAt.mul
    (((inverseContinuous.smul (firstRow.add (muContinuous.smul forceFirstContinuous))).norm.pow 2).add
      ((inverseContinuous.smul (secondRow.add (muContinuous.smul forceSecondContinuous))).norm.pow 2))

theorem lowDerivativeDensity_bound (parameters : PhaseParameters) (length radius : ℝ)
    (lengthPositive : 0 < length) (mode : LowAnnularMode) (positive : 0 < radius) (bounded : radius ≤ 1)
    (first second forcingFirst forcingSecond : E) :
    lowDerivativeDensity parameters length radius mode first second forcingFirst forcingSecond ≤
      (8 * lowReferenceCoefficientConstant parameters length ^ 2) *
        (radius ^ (-(7 / 2 : ℝ)) * (‖first‖ ^ 2 + ‖second‖ ^ 2)) +
      2 * (radius ^ (-(7 / 2 : ℝ)) * (‖forcingFirst‖ ^ 2 + ‖forcingSecond‖ ^ 2)) := by
  have result := mul_le_mul_of_nonneg_left
    (lowReferenceDerivative_pair_bound parameters length radius lengthPositive mode positive bounded
      first second forcingFirst forcingSecond) (Real.rpow_pos_of_pos positive (-(7 / 2 : ℝ))).le
  unfold lowDerivativeDensity
  nlinarith only [result]

end Hilbert
end Grad.AnnularLowVolterra
