import AKBC22OriginalCoreCommutations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.NonlinearRange Grad.FlatSourceProjection Grad.QuotientProjection
open Grad.FinitePhysicalJetLift Grad.AxisSplit Grad.OriginalKernelRetainedDecay

theorem originalRotation_constant {parameters : PhaseParameters} {dimension : ℕ}
    (value : ComplexEuclidean dimension) :
    rotationCore parameters (constantCore parameters value)=0 := by
  simp only [rotationCore,LinearMap.sub_apply,LinearMap.comp_apply,originalConstant_partial,map_zero,sub_zero]

theorem originalRotation_affine {parameters : PhaseParameters} (length : ℝ) (state : QuotientState parameters) :
    rotationCore parameters (affineStateCore parameters length state)=
      physicalVariationAffine state.1 (rotationCore parameters state.2.1) := by
  simp only [affineStateCore,stateField,stateScalar,map_add,map_smul,eTConstantCore,
    originalRotation_constant,smul_zero,add_zero,← originalTime_rotation,originalRotation_valueMap,
    physicalVariationAffine]
  rfl

/-- The literal fourth quotient row is the normalized axial force identity
for the same retained scalar xi. Its projection is the original P=1-Pi. -/
theorem originalHomogeneous_thirdIdentity (parameters : PhaseParameters) (length : ℝ)
    (state : QuotientState parameters) (vector : ACore parameters 3) (scalar : ACore parameters 1)
    (homogeneous : quotientRowsDerivative parameters length 1 state ![(0,vector,scalar)]=0) :
    removeAngularCore parameters
      (rotationCore parameters (dotOperation parameters vector (affineStateCore parameters length state))-
        (2 : ℂ) • dotOperation parameters vector
          (rotationCore parameters (affineStateCore parameters length state))) -
      timeDerivativeCore parameters (originalKernelXi state.2.1 vector scalar)=0 := by
  have row : removeAngularCore parameters
      (dotOperation parameters (rotationCore parameters vector) (affineStateCore parameters length state)+
        dotOperation parameters (rotationCore parameters state.2.1) (physicalVariationAffine state.1 vector)-
        timeDerivativeCore parameters scalar)=0 := by
    have literal := congrArg (fun rows : QuotientRows parameters => rows 3)
      ((quotientRowsDerivative_etaZero parameters length state vector scalar).symm.trans homogeneous)
    exact literal
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
  rw [originalKernelXi,originalTime_removeAngular,← map_sub,algebra]
  exact row

end Grad.OriginalKernelCovariantRecovery
