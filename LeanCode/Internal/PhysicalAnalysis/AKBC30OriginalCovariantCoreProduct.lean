import AKBC29OriginalCoreFrameColumns

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.NonlinearRange Grad.OriginalKernelRetainedDecay
open Grad.SourceCollar Grad.SourceCollarCoefficients Grad.GaugeCoefficients.Physical.Ledger

def originalScalarTripletCore {parameters : PhaseParameters} (entries : Fin 3 → ACore parameters 1) : ACore parameters 3 :=
  valueMapCore parameters (matrixUnit (0 : Fin 3) (0 : Fin 1)) (entries 0)+
    valueMapCore parameters (matrixUnit (1 : Fin 3) (0 : Fin 1)) (entries 1)+
    valueMapCore parameters (matrixUnit (2 : Fin 3) (0 : Fin 1)) (entries 2)

theorem originalScalarTripletCore_value {parameters : PhaseParameters} (entries : Fin 3 → ACore parameters 1)
    (point : ClosedDisk) (axial : ℝ) (component : Fin 3) :
    coreValue (originalScalarTripletCore entries) point axial component=coreValue (entries component) point axial 0 := by
  fin_cases component <;> simp [originalScalarTripletCore,coreValue_add,coreValue_valueMap,matrixUnit_apply,operatorBasis]

def originalCovariantCore (parameters : PhaseParameters) (length epsilon : ℝ)
    (base vector : ACore parameters 3) (rotated : Bool) : ACore parameters 3 :=
  originalScalarTripletCore (fun column => dotOperation parameters
    (if rotated then rotationCore parameters (originalFrameColumnCore parameters length epsilon base column)
      else originalFrameColumnCore parameters length epsilon base column) vector)

theorem originalCovariantCore_value (parameters : PhaseParameters) (length epsilon : ℝ) (nonzero : length≠0)
    (base vector : ACore parameters 3) (point : ClosedDisk) (axial : ℝ) :
    coreValue (originalCovariantCore parameters length epsilon base vector false) point axial=
      WithLp.toLp 2 ((originalPhysicalFrameMatrix parameters length epsilon base axial point).transpose.mulVec
        (coreValue vector point axial)) := by
  apply PiLp.ext
  intro component
  rw [originalCovariantCore,originalScalarTripletCore_value,if_neg Bool.false_ne_true,coreValue_dotOperation]
  change (∑ row,coreValue (originalFrameColumnCore parameters length epsilon base component) point axial row*
    coreValue vector point axial row)=_
  simp_rw [originalFrameColumnCore_value parameters length epsilon nonzero base]
  rfl

theorem originalRotatedCovariantCore_value (parameters : PhaseParameters) (length epsilon : ℝ) (nonzero : length≠0)
    (base vector : ACore parameters 3) (point : ClosedDisk) (axial : ℝ) :
    coreValue (originalCovariantCore parameters length epsilon base vector true) point axial=
      WithLp.toLp 2 ((rotatedPhysicalFrameMatrix parameters 1 1 epsilon base axial point *
        Matrix.diagonal ![1,1,(length : ℂ)⁻¹]).transpose.mulVec (coreValue vector point axial)) := by
  apply PiLp.ext
  intro component
  rw [originalCovariantCore,originalScalarTripletCore_value,if_pos rfl,coreValue_dotOperation]
  change (∑ row,coreValue (rotationCore parameters (originalFrameColumnCore parameters length epsilon base component)) point axial row*
    coreValue vector point axial row)=_
  simp_rw [originalRotatedFrameColumnCore_value parameters length epsilon nonzero base]
  rfl

theorem originalCovariantCore_rotation (parameters : PhaseParameters) (length epsilon : ℝ)
    (base vector : ACore parameters 3) :
    rotationCore parameters (originalCovariantCore parameters length epsilon base vector false)=
      originalCovariantCore parameters length epsilon base vector true+
        originalCovariantCore parameters length epsilon base (rotationCore parameters vector) false := by
  simp only [originalCovariantCore,originalScalarTripletCore,Bool.false_eq_true,if_false,if_true,map_add,
    originalRotation_valueMap,originalDot_rotation]
  abel

end Grad.OriginalKernelCovariantRecovery
