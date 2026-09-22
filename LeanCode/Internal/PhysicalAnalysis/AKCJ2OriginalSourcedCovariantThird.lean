import AKCJ1OriginalSourcedThirdCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.NonlinearRange Grad.QuotientProjection Grad.FinitePhysicalJetLift
open Grad.OriginalKernelRetainedDecay Grad.OriginalKernelCovariantRecovery
open Grad.GaugeCoefficients.Physical.Ledger

/-- Exact normalized fourth original row on literal covariant cores.
This equality retains the arbitrary source and both frame derivatives. -/
theorem originalThirdRow_covariant (parameters : PhaseParameters) (length epsilon : ℝ)
    (base vector : ACore parameters 3) (scalar : ACore parameters 1) (state : QuotientState parameters)
    (sameBase : state.2.1=planarReferenceCore parameters+base) (sameEpsilon : state.1=(epsilon : ℂ)) :
    rotationCore parameters
      (valueMapCore parameters (matrixUnit (0 : Fin 1) (2 : Fin 3))
        (originalCovariantCore parameters length epsilon base vector false))+
      removeAngularCore parameters ((-2 : ℂ) •
        valueMapCore parameters (matrixUnit (0 : Fin 1) (2 : Fin 3))
          (originalCovariantCore parameters length epsilon base vector true))-
      (length : ℂ)⁻¹ • timeDerivativeCore parameters (originalKernelXi state.2.1 vector scalar)=
      (length : ℂ)⁻¹ • quotientRowsDerivative parameters length 1 state ![(0,vector,scalar)] 3 := by
  have affine : affineStateCore parameters length state=
      affineStateCore parameters length ((epsilon : ℂ),planarReferenceCore parameters+base,0) := by
    change timeDerivativeCore parameters state.2.1+state.1 • valueMapCore parameters tangentGeneratorMap state.2.1+
      (length : ℂ) • eTConstantCore parameters=_
    rw [sameBase,sameEpsilon]
    rfl
  have raw := originalThirdRow_retainedXi parameters length state vector scalar
  rw [affine,map_sub,map_smul,originalRemoveAngular_rotation] at raw
  rw [originalCovariantCore_axial,originalRotatedCovariantCore_axial,map_smul,map_smul,map_smul]
  have scaled := congrArg ((length : ℂ)⁻¹ • ·) raw
  simp only [smul_sub,smul_smul] at scaled
  convert scaled using 1
  module

/-- Restore the original physical length in the exact source row. -/
theorem originalThirdRow_covariant_unscaled (parameters : PhaseParameters) (length epsilon : ℝ)
    (nonzero : length≠0) (base vector : ACore parameters 3) (scalar : ACore parameters 1)
    (state : QuotientState parameters)
    (sameBase : state.2.1=planarReferenceCore parameters+base) (sameEpsilon : state.1=(epsilon : ℂ)) :
    (length : ℂ) • rotationCore parameters
      (valueMapCore parameters (matrixUnit (0 : Fin 1) (2 : Fin 3))
        (originalCovariantCore parameters length epsilon base vector false))-
      timeDerivativeCore parameters (originalKernelXi state.2.1 vector scalar)+
      (length : ℂ) • removeAngularCore parameters ((-2 : ℂ) •
        valueMapCore parameters (matrixUnit (0 : Fin 1) (2 : Fin 3))
          (originalCovariantCore parameters length epsilon base vector true))=
      quotientRowsDerivative parameters length 1 state ![(0,vector,scalar)] 3 := by
  have scaled := congrArg ((length : ℂ) • ·)
    (originalThirdRow_covariant parameters length epsilon base vector scalar state sameBase sameEpsilon)
  simp only [smul_sub,smul_add,smul_smul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr nonzero),one_smul] at scaled
  convert scaled using 1
  module

end Grad.OriginalCoreRealization
