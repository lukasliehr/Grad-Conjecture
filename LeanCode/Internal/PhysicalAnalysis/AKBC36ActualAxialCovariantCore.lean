import AKBC35OriginalCircleCoreAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.NonlinearRange Grad.QuotientProjection Grad.FinitePhysicalJetLift
open Grad.OriginalKernelRetainedDecay Grad.GaugeCoefficients.Physical.Ledger

theorem originalScalarTripletCore_coordinate {parameters : PhaseParameters}
    (entries : Fin 3 → ACore parameters 1) (coordinate : Fin 3) :
    valueMapCore parameters (matrixUnit (0 : Fin 1) coordinate) (originalScalarTripletCore entries)=entries coordinate := by
  apply coreValue_ext
  intro point axial
  apply PiLp.ext
  intro component
  fin_cases component
  rw [coreValue_valueMap]
  simpa [matrixUnit_apply,operatorBasis] using originalScalarTripletCore_value entries point axial coordinate

theorem originalCovariantCore_axial (parameters : PhaseParameters) (length epsilon : ℝ)
    (base vector : ACore parameters 3) :
    valueMapCore parameters (matrixUnit (0 : Fin 1) (2 : Fin 3))
      (originalCovariantCore parameters length epsilon base vector false)=
      (length : ℂ)⁻¹ • dotOperation parameters vector
        (affineStateCore parameters length ((epsilon : ℂ),planarReferenceCore parameters+base,0)) := by
  rw [originalCovariantCore,originalScalarTripletCore_coordinate]
  simp only [Bool.false_eq_true,if_false,originalFrameColumnCore,Matrix.cons_val,map_smul,
    LinearMap.smul_apply]
  rw [originalDot_comm]

theorem originalRotatedCovariantCore_axial (parameters : PhaseParameters) (length epsilon : ℝ)
    (base vector : ACore parameters 3) :
    valueMapCore parameters (matrixUnit (0 : Fin 1) (2 : Fin 3))
      (originalCovariantCore parameters length epsilon base vector true)=
      (length : ℂ)⁻¹ • dotOperation parameters vector
        (rotationCore parameters (affineStateCore parameters length ((epsilon : ℂ),planarReferenceCore parameters+base,0))) := by
  rw [originalCovariantCore,originalScalarTripletCore_coordinate]
  simp only [if_true,originalFrameColumnCore,Matrix.cons_val,map_smul,LinearMap.smul_apply]
  rw [originalDot_comm]

theorem originalRemoveAngular_rotation {parameters : PhaseParameters} (field : ACore parameters 1) :
    removeAngularCore parameters (rotationCore parameters field)=rotationCore parameters field := by
  change rotationCore parameters field-angularCore parameters 0 (rotationCore parameters field)=_
  rw [angularCore_rotationCore_zero,sub_zero]

/-- The actual fourth quotient row becomes the third normalized force row
on original smooth covariant cores, with its original projection and L. -/
theorem originalHomogeneous_axialCovariantCore (parameters : PhaseParameters) (length epsilon : ℝ)
    (base vector : ACore parameters 3) (scalar : ACore parameters 1) (state : QuotientState parameters)
    (sameBase : state.2.1=planarReferenceCore parameters+base) (sameEpsilon : state.1=(epsilon : ℂ))
    (homogeneous : quotientRowsDerivative parameters length 1 state ![(0,vector,scalar)]=0) :
    rotationCore parameters
      (valueMapCore parameters (matrixUnit (0 : Fin 1) (2 : Fin 3))
        (originalCovariantCore parameters length epsilon base vector false))+
      removeAngularCore parameters ((-2 : ℂ) •
        valueMapCore parameters (matrixUnit (0 : Fin 1) (2 : Fin 3))
          (originalCovariantCore parameters length epsilon base vector true))-
      (length : ℂ)⁻¹ • timeDerivativeCore parameters (originalKernelXi state.2.1 vector scalar)=0 := by
  have affine : affineStateCore parameters length state=
      affineStateCore parameters length ((epsilon : ℂ),planarReferenceCore parameters+base,0) := by
    change timeDerivativeCore parameters state.2.1+state.1 • valueMapCore parameters tangentGeneratorMap state.2.1+
      (length : ℂ) • eTConstantCore parameters=_
    rw [sameBase,sameEpsilon]
    rfl
  have raw := originalHomogeneous_thirdIdentity parameters length state vector scalar homogeneous
  rw [affine,map_sub,map_smul,originalRemoveAngular_rotation] at raw
  rw [originalCovariantCore_axial,originalRotatedCovariantCore_axial,map_smul,map_smul,map_smul]
  have scaled := congrArg ((length : ℂ)⁻¹ • ·) raw
  simp only [smul_sub,smul_smul,smul_zero] at scaled
  convert scaled using 1
  module

end Grad.OriginalKernelCovariantRecovery
