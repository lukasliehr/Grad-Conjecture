import AEC6ActualEnergySlopeContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators
namespace Grad.AnnularLowVolterra
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularVariational Grad.CartesianState

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Integrating the actual reference equation yields its original rho/mu
endpoint energy plus rho-L2 coercive bulk term. Constants are independent
of the lower radius, the Fourier mode, and any finite cutoff. -/
theorem lowPairEnergy_integrated_bound (parameters : PhaseParameters) (length lower upper : ℝ)
    (lengthPositive : 0 < length) (mode : LowAnnularMode)
    (positive : 0 < lower) (ordered : lower ≤ upper)
    (first second forcingFirst forcingSecond : ℝ → E)
    (forceFirstContinuous : ∀ radius ∈ Icc lower upper, ContinuousAt forcingFirst radius)
    (forceSecondContinuous : ∀ radius ∈ Icc lower upper, ContinuousAt forcingSecond radius)
    (firstDerivative : ∀ radius ∈ Icc lower upper, HasDerivAt first
      (lowReferenceFirst parameters length radius mode (first radius) (second radius) +
        lowMu length radius mode.val.2 • forcingFirst radius) radius)
    (secondDerivative : ∀ radius ∈ Icc lower upper, HasDerivAt second
      (lowReferenceSecond parameters length radius mode (first radius) (second radius) +
        lowMu length radius mode.val.2 • forcingSecond radius) radius) :
    lowPairEnergy length upper mode (first upper) (second upper) +
      (lowEta length parameters.gamma / 2) *
        (∫ radius in lower..upper, radius ^ (-(7 / 2 : ℝ)) * (‖first radius‖ ^ 2 + ‖second radius‖ ^ 2)) ≤
    lowPairEnergy length lower mode (first lower) (second lower) +
      (4 / lowEta length parameters.gamma) *
        (∫ radius in lower..upper, radius ^ (-(7 / 2 : ℝ)) * (‖forcingFirst radius‖ ^ 2 + ‖forcingSecond radius‖ ^ 2)) := by
  let slope := fun radius => lowPairEnergySlope parameters length radius mode
    (first radius) (second radius) (forcingFirst radius) (forcingSecond radius)
  let mass := fun radius => radius ^ (-(7 / 2 : ℝ)) * (‖first radius‖ ^ 2 + ‖second radius‖ ^ 2)
  let forceMass := fun radius => radius ^ (-(7 / 2 : ℝ)) * (‖forcingFirst radius‖ ^ 2 + ‖forcingSecond radius‖ ^ 2)
  have unordered : uIcc lower upper = Icc lower upper := uIcc_of_le ordered
  have slopeContinuous : ContinuousOn slope (uIcc lower upper) := by
    rw [unordered]
    intro radius member
    exact (lowPairEnergySlope_continuousAt parameters length radius mode (positive.trans_le member.1)
      first second forcingFirst forcingSecond (firstDerivative radius member).continuousAt
      (secondDerivative radius member).continuousAt (forceFirstContinuous radius member)
      (forceSecondContinuous radius member)).continuousWithinAt
  have massContinuous : ContinuousOn mass (uIcc lower upper) := by
    rw [unordered]
    intro radius member
    exact (lowWeightedSquare_continuousAt radius (positive.trans_le member.1) first second
      (firstDerivative radius member).continuousAt (secondDerivative radius member).continuousAt).continuousWithinAt
  have forceContinuous : ContinuousOn forceMass (uIcc lower upper) := by
    rw [unordered]
    intro radius member
    exact (lowWeightedSquare_continuousAt radius (positive.trans_le member.1) forcingFirst forcingSecond
      (forceFirstContinuous radius member) (forceSecondContinuous radius member)).continuousWithinAt
  have slopeIntegrable : IntervalIntegrable slope volume lower upper := slopeContinuous.intervalIntegrable
  have massIntegrable : IntervalIntegrable mass volume lower upper := massContinuous.intervalIntegrable
  have forceIntegrable : IntervalIntegrable forceMass volume lower upper := forceContinuous.intervalIntegrable
  have derivative : ∀ radius ∈ uIcc lower upper,
      HasDerivAt (fun point => lowPairEnergy length point mode (first point) (second point)) (slope radius) radius := by
    rw [unordered]
    intro radius member
    exact lowPairEnergy_hasDerivAt parameters length radius mode (positive.trans_le member.1)
      first second (forcingFirst radius) (forcingSecond radius)
      (firstDerivative radius member) (secondDerivative radius member)
  have fundamental := intervalIntegral.integral_eq_sub_of_hasDerivAt derivative slopeIntegrable
  have integrated := intervalIntegral.integral_mono_on ordered
    (slopeIntegrable.add (massIntegrable.const_mul (lowEta length parameters.gamma / 2)))
    (forceIntegrable.const_mul (4 / lowEta length parameters.gamma))
    (fun radius member => by
      simpa only [slope, mass, forceMass, mul_assoc] using
        lowPairEnergySlope_bound parameters length radius lengthPositive mode (positive.trans_le member.1)
          (first radius) (second radius) (forcingFirst radius) (forcingSecond radius))
  rw [intervalIntegral.integral_add slopeIntegrable (massIntegrable.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, fundamental] at integrated
  linarith

end Hilbert
end Grad.AnnularLowVolterra
