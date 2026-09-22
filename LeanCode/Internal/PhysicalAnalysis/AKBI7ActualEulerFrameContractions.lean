import AKBI6OriginalFourierRadialEuler
import AKAT1LiteralRadialForceContraction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.FinitePhysicalJetLift Grad.AxisSplit Grad.NonlinearProduct
open Grad.OriginalKernelRetainedDecay Grad.OriginalKernelCovariantRecovery
open Grad.AnnularReconstruction
open Grad.SourceCollar Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.Ledger Grad.ActualCurrentPrimitives Grad.ActualSmoothPhysicalField
open Grad.GaugeCoefficients.Physical.GaugeTransfer

theorem originalCore_euler_value {dimension : ℕ} {parameters : PhaseParameters} (field : ACore parameters dimension)
    (point : ClosedDisk) (axial : ℝ) :
    coreValue (eulerCore parameters field) point axial=
      (point.val 0 : ℂ) • coreValue (partialCore parameters 0 field) point axial+
        (point.val 1 : ℂ) • coreValue (partialCore parameters 1 field) point axial := by
  rw [eulerCore,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.comp_apply,coreValue_add,
    coreValue_coordinate,coreValue_coordinate,Complex.coe_smul,Complex.coe_smul]

theorem originalRadialFrame_dot (parameters : PhaseParameters) (length epsilon : ℝ)
    (base field : ACore parameters 3) (radius : RadialPoint) (angles : ℝ×ℝ) :
    (radius.val : ℂ) • originalPolarRadialValue
      (WithLp.toLp 2 ((originalPhysicalFrameMatrix parameters length epsilon base angles.2
        (Grad.SourceCollarDivision.polarClosedPoint radius.val angles.1 radius.property.1 radius.property.2)).transpose.mulVec
        (originalCoreCircle parameters field radius angles))) angles.1=
      originalCoreCircle parameters (dotOperation parameters (eulerCore parameters (planarReferenceCore parameters+base)) field) radius angles := by
  apply PiLp.ext
  intro row
  fin_cases row
  change _=coreValue (dotOperation parameters (eulerCore parameters (planarReferenceCore parameters+base)) field) _ _ 0
  rw [coreValue_dotOperation,originalCore_euler_value]
  simp only [Grad.NonlinearQuotient.complexDot,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  simp_rw [originalTotalFirstDerivative_frame parameters length epsilon base]
  simp [originalPolarRadialValue,matrixUnit_apply,operatorBasis,Matrix.mulVec,dotProduct,Matrix.transpose_apply,
    Fin.sum_univ_succ,originalCoreCircle,Grad.SourceCollarDivision.polarClosedPoint,polarPlane,Grad.BoundaryTrace.collarPlane]
  ring

theorem originalRotatedEulerColumns {parameters : PhaseParameters} {dimension : ℕ} (field : ACore parameters dimension) :
    coordinateCore parameters 0 (rotationCore parameters (partialCore parameters 0 field))+
      coordinateCore parameters 1 (rotationCore parameters (partialCore parameters 1 field))=
      rotationCore parameters (eulerCore parameters field)-rotationCore parameters field := by
  simp [rotationCore,eulerCore,partialCore_coordinateCore,map_add,map_sub,coordinateCore_commute 1 0]
  abel

theorem originalRotatedRadialFrame_dot (parameters : PhaseParameters) (length epsilon : ℝ) (nonzero : length≠0)
    (base field : ACore parameters 3) (radius : RadialPoint) (angles : ℝ×ℝ) :
    (radius.val : ℂ) • originalPolarRadialValue
      (WithLp.toLp 2 ((rotatedPhysicalFrameMatrix parameters 1 1 epsilon base angles.2
        (Grad.SourceCollarDivision.polarClosedPoint radius.val angles.1 radius.property.1 radius.property.2)*
          Matrix.diagonal ![1,1,(length : ℂ)⁻¹]).transpose.mulVec (originalCoreCircle parameters field radius angles))) angles.1=
    originalCoreCircle parameters
      (dotOperation parameters
        (rotationCore parameters (eulerCore parameters (planarReferenceCore parameters+base))-
          rotationCore parameters (planarReferenceCore parameters+base)) field) radius angles := by
  rw [← originalRotatedEulerColumns]
  apply PiLp.ext
  intro row
  fin_cases row
  change _=coreValue (dotOperation parameters _ field) _ _ 0
  rw [coreValue_dotOperation,coreValue_add,coreValue_coordinate,coreValue_coordinate]
  simp only [Grad.NonlinearQuotient.complexDot,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  have first := originalRotatedFrameColumnCore_value parameters length epsilon nonzero base 0
  have second := originalRotatedFrameColumnCore_value parameters length epsilon nonzero base 1
  change ∀ point axial row,coreValue (rotationCore parameters (partialCore parameters 0 (planarReferenceCore parameters+base))) point axial row=_ at first
  change ∀ point axial row,coreValue (rotationCore parameters (partialCore parameters 1 (planarReferenceCore parameters+base))) point axial row=_ at second
  simp_rw [first,second]
  simp [originalPolarRadialValue,matrixUnit_apply,operatorBasis,Matrix.mulVec,dotProduct,Matrix.transpose_apply,
    Fin.sum_univ_succ,originalCoreCircle,Grad.SourceCollarDivision.polarClosedPoint,polarPlane,Grad.BoundaryTrace.collarPlane]
  ring

end Grad.OriginalKernelHomogeneousGraph
