import AKCJ8OriginalThirdCartesianValue

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearRange Grad.OriginalKernelCovariantRecovery
open Grad.GaugeCoefficients.Physical.Ledger Grad.SourceCollarCoefficients Grad.SourceCollar
open Grad.ActualPolarEquations Grad.ActualForceMatrixFidelity Grad.GaugeCoefficients.Physical.Allocation

/-- Literal original rotated-frame correction in the scalar third row. -/
theorem originalThirdForce_value (parameters : PhaseParameters) (length epsilon : ℝ)
    (nonzero : length≠0) (base vector : ACore parameters 3) (point : ClosedDisk) (axial angle : ℝ) :
    (-2 : ℂ) * coreValue (originalCovariantCore parameters length epsilon base vector true) point axial 2=
      matrixPairing ((-2 : ℂ) • physicalToroidalVector)
        (rotatedPhysicalFrameMatrix parameters 1 1 epsilon base axial point * Matrix.diagonal ![1,1,(length : ℂ)⁻¹]).transpose
        (coreValue vector point axial) := by
  have actual := originalForcePolarValue_pairing (1 : Fin 2) angle
    (rotatedPhysicalFrameMatrix parameters 1 1 epsilon base axial point * Matrix.diagonal ![1,1,(length : ℂ)⁻¹]).transpose
    (coreValue vector point axial)
  rw [← originalRotatedCovariantCore_value parameters length epsilon nonzero base vector point axial] at actual
  simpa only [originalForcePolarValue,show (1 : Fin 2)≠0 by decide,if_false,
    PiLp.smul_apply,matrixUnit_apply,operatorBasis,PiLp.single_apply,ite_true,smul_eq_mul,mul_one] using actual.symm

end Grad.OriginalCoreRealization
