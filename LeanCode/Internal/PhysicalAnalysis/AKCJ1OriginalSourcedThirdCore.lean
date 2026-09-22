import AKBC36ActualAxialCovariantCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.NonlinearRange Grad.FlatSourceProjection Grad.QuotientProjection
open Grad.FinitePhysicalJetLift Grad.AxisSplit Grad.OriginalKernelRetainedDecay
open Grad.OriginalKernelCovariantRecovery

/-- The genuine fourth original derivative row, expressed through the same
retained scalar Xi. No homogeneous equation is assumed. -/
theorem originalThirdRow_retainedXi (parameters : PhaseParameters) (length : ℝ)
    (state : QuotientState parameters) (vector : ACore parameters 3) (scalar : ACore parameters 1) :
    removeAngularCore parameters
      (rotationCore parameters (dotOperation parameters vector (affineStateCore parameters length state))-
        (2 : ℂ) • dotOperation parameters vector
          (rotationCore parameters (affineStateCore parameters length state))) -
      timeDerivativeCore parameters (originalKernelXi state.2.1 vector scalar)=
        quotientRowsDerivative parameters length 1 state ![(0,vector,scalar)] 3 := by
  have algebra : rotationCore parameters (dotOperation parameters vector (affineStateCore parameters length state))-
        (2 : ℂ) • dotOperation parameters vector (rotationCore parameters (affineStateCore parameters length state))-
        timeDerivativeCore parameters (scalar-dotOperation parameters (rotationCore parameters state.2.1) vector)=
      dotOperation parameters (rotationCore parameters vector) (affineStateCore parameters length state)+
        dotOperation parameters (rotationCore parameters state.2.1) (physicalVariationAffine state.1 vector)-
        timeDerivativeCore parameters scalar := by
    rw [originalDot_rotation,map_sub,originalDot_time,originalTime_rotation,originalRotation_affine]
    simp only [physicalVariationAffine,map_add,map_smul]
    rw [originalDot_comm vector (timeDerivativeCore parameters (rotationCore parameters state.2.1)),
      originalDot_comm vector (valueMapCore parameters tangentGeneratorMap (rotationCore parameters state.2.1)),
      originalDot_tangentSkew (rotationCore parameters state.2.1) vector,← originalTime_rotation]
    module
  rw [originalKernelXi,originalTime_removeAngular,← map_sub,algebra,quotientRowsDerivative_etaZero]
  rfl

end Grad.OriginalCoreRealization
