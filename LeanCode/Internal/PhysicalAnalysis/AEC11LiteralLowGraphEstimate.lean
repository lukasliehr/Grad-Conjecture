import AEC10DerivativeDensityContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators
namespace Grad.AnnularLowVolterra
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularVariational Grad.CartesianState

def lowReferenceGraphConstant (parameters : PhaseParameters) (length : ℝ) : ℝ :=
  ((1 + 8 * lowReferenceCoefficientConstant parameters length ^ 2) / (lowEta length parameters.gamma / 2)) *
    (1 + 4 / lowEta length parameters.gamma) + 2

theorem lowReferenceGraphConstant_pos (parameters : PhaseParameters) (length : ℝ)
    (lengthPositive : 0 < length) : 0 < lowReferenceGraphConstant parameters length := by
  have etaPositive := lowEta_pos length parameters.gamma lengthPositive parameters.gamma_pos
  unfold lowReferenceGraphConstant
  positivity

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Literal BE18 Y-norm estimate for actual reference rows. The derivative
is the real derivative of the solution, normalized by the original mu.
The right side is exactly the incoming energy plus rho-weighted forcing. -/
theorem lowReferenceGraph_integrated_bound (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (mode : LowAnnularMode)
    (positive : 0 < lower) (ordered : lower ≤ 1)
    (first second forcingFirst forcingSecond : ℝ → E)
    (forceFirstContinuous : ∀ radius ∈ Icc lower 1, ContinuousAt forcingFirst radius)
    (forceSecondContinuous : ∀ radius ∈ Icc lower 1, ContinuousAt forcingSecond radius)
    (firstDerivative : ∀ radius ∈ Icc lower 1, HasDerivAt first
      (lowReferenceFirst parameters length radius mode (first radius) (second radius) +
        lowMu length radius mode.val.2 • forcingFirst radius) radius)
    (secondDerivative : ∀ radius ∈ Icc lower 1, HasDerivAt second
      (lowReferenceSecond parameters length radius mode (first radius) (second radius) +
        lowMu length radius mode.val.2 • forcingSecond radius) radius) :
    (∫ radius in lower..1, radius ^ (-(7 / 2 : ℝ)) *
      (‖first radius‖ ^ 2 + ‖second radius‖ ^ 2 +
        ‖(lowMu length radius mode.val.2)⁻¹ • deriv first radius‖ ^ 2 +
        ‖(lowMu length radius mode.val.2)⁻¹ • deriv second radius‖ ^ 2)) ≤
    lowReferenceGraphConstant parameters length *
      (lowPairEnergy length lower mode (first lower) (second lower) +
        ∫ radius in lower..1, radius ^ (-(7 / 2 : ℝ)) * (‖forcingFirst radius‖ ^ 2 + ‖forcingSecond radius‖ ^ 2)) := by
  let mass := fun radius => radius ^ (-(7 / 2 : ℝ)) * (‖first radius‖ ^ 2 + ‖second radius‖ ^ 2)
  let forceMass := fun radius => radius ^ (-(7 / 2 : ℝ)) * (‖forcingFirst radius‖ ^ 2 + ‖forcingSecond radius‖ ^ 2)
  let slopeMass := fun radius => lowDerivativeDensity parameters length radius mode
    (first radius) (second radius) (forcingFirst radius) (forcingSecond radius)
  have unordered : uIcc lower 1 = Icc lower 1 := uIcc_of_le ordered
  have massContinuous : ContinuousOn mass (uIcc lower 1) := by
    rw [unordered]
    intro radius member
    exact (lowWeightedSquare_continuousAt radius (positive.trans_le member.1) first second
      (firstDerivative radius member).continuousAt (secondDerivative radius member).continuousAt).continuousWithinAt
  have forceContinuous : ContinuousOn forceMass (uIcc lower 1) := by
    rw [unordered]
    intro radius member
    exact (lowWeightedSquare_continuousAt radius (positive.trans_le member.1) forcingFirst forcingSecond
      (forceFirstContinuous radius member) (forceSecondContinuous radius member)).continuousWithinAt
  have slopeContinuous : ContinuousOn slopeMass (uIcc lower 1) := by
    rw [unordered]
    intro radius member
    exact (lowDerivativeDensity_continuousAt parameters length radius mode (positive.trans_le member.1)
      first second forcingFirst forcingSecond (firstDerivative radius member).continuousAt
      (secondDerivative radius member).continuousAt (forceFirstContinuous radius member)
      (forceSecondContinuous radius member)).continuousWithinAt
  have massIntegrable : IntervalIntegrable mass volume lower 1 := massContinuous.intervalIntegrable
  have forceIntegrable : IntervalIntegrable forceMass volume lower 1 := forceContinuous.intervalIntegrable
  have slopeIntegrable : IntervalIntegrable slopeMass volume lower 1 := slopeContinuous.intervalIntegrable
  have graphIdentity : (∫ radius in lower..1, radius ^ (-(7 / 2 : ℝ)) *
      (‖first radius‖ ^ 2 + ‖second radius‖ ^ 2 +
        ‖(lowMu length radius mode.val.2)⁻¹ • deriv first radius‖ ^ 2 +
        ‖(lowMu length radius mode.val.2)⁻¹ • deriv second radius‖ ^ 2)) =
      (∫ radius in lower..1, mass radius) + ∫ radius in lower..1, slopeMass radius := by
    rw [← intervalIntegral.integral_add massIntegrable slopeIntegrable]
    apply intervalIntegral.integral_congr
    intro radius member
    rw [unordered] at member
    dsimp only
    rw [(firstDerivative radius member).deriv, (secondDerivative radius member).deriv]
    dsimp [mass, slopeMass, lowDerivativeDensity]
    ring
  rw [graphIdentity]
  have slopeBound := intervalIntegral.integral_mono_on ordered slopeIntegrable
    ((massIntegrable.const_mul (8 * lowReferenceCoefficientConstant parameters length ^ 2)).add (forceIntegrable.const_mul 2))
    (fun radius member => lowDerivativeDensity_bound parameters length radius lengthPositive mode
      (positive.trans_le member.1) member.2 (first radius) (second radius) (forcingFirst radius) (forcingSecond radius))
  rw [intervalIntegral.integral_add (massIntegrable.const_mul _) (forceIntegrable.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at slopeBound
  have energy := lowPairEnergy_integrated_bound parameters length lower 1 lengthPositive mode positive ordered
    first second forcingFirst forcingSecond forceFirstContinuous forceSecondContinuous firstDerivative secondDerivative
  have outerNonnegative : 0 ≤ lowPairEnergy length 1 mode (first 1) (second 1) := by
    unfold lowPairEnergy
    exact mul_nonneg (lowEnergyDensity_pos length 1 mode.val.2 zero_lt_one).le (by positivity)
  have incomingNonnegative : 0 ≤ lowPairEnergy length lower mode (first lower) (second lower) := by
    unfold lowPairEnergy
    exact mul_nonneg (lowEnergyDensity_pos length lower mode.val.2 positive).le (by positivity)
  have forceNonnegative : 0 ≤ ∫ radius in lower..1, forceMass radius :=
    intervalIntegral.integral_nonneg ordered (fun radius member =>
      mul_nonneg (Real.rpow_pos_of_pos (positive.trans_le member.1) _).le (by positivity))
  have etaPositive := lowEta_pos length parameters.gamma lengthPositive parameters.gamma_pos
  let factor := (1 + 8 * lowReferenceCoefficientConstant parameters length ^ 2) / (lowEta length parameters.gamma / 2)
  have factorNonnegative : 0 ≤ factor := by dsimp [factor]; positivity
  have factorCancel : factor * (lowEta length parameters.gamma / 2) =
      1 + 8 * lowReferenceCoefficientConstant parameters length ^ 2 :=
    div_mul_cancel₀ _ (by positivity)
  have bulkBound : (lowEta length parameters.gamma / 2) * (∫ radius in lower..1, mass radius) ≤
      lowPairEnergy length lower mode (first lower) (second lower) +
        (4 / lowEta length parameters.gamma) * (∫ radius in lower..1, forceMass radius) := by
    linarith only [energy, outerNonnegative]
  have scaled := mul_le_mul_of_nonneg_left bulkBound factorNonnegative
  rw [← mul_assoc, factorCancel] at scaled
  have extraIncoming := mul_nonneg
    (show 0 ≤ factor * (4 / lowEta length parameters.gamma) + 2 by positivity) incomingNonnegative
  have extraForcing := mul_nonneg factorNonnegative forceNonnegative
  change _ ≤ (factor * (1 + 4 / lowEta length parameters.gamma) + 2) * _
  nlinarith only [slopeBound, scaled, extraIncoming, extraForcing]

end Hilbert
end Grad.AnnularLowVolterra
