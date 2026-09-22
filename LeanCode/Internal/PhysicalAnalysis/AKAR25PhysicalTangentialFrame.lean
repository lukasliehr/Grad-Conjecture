import AKAR23ActualTotalFrameRotation
import AKAR19CircleRepresentationAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped BigOperators
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.FinitePhysicalJetLift Grad.AxisSplit
open Grad.SourceCollar Grad.GaugeCoefficients.Physical.RadialLedger Grad.SourceCollarDivision
open Grad.SourceCollarCoefficients Grad.GaugeCoefficients.Physical.Frame Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularReconstruction Grad.GaugeCoefficients.Physical.Allocation

theorem originalCoreCircleTrace_add {dimension : ℕ} (parameters : PhaseParameters)
    (first second : ACore parameters dimension) (radius : RadialPoint) :
    originalCoreCircleTrace parameters (first+second) radius =
      originalCoreCircleTrace parameters first radius+originalCoreCircleTrace parameters second radius := by
  apply (originalCoreCircleTrace_represents parameters (first+second) radius).unique
  have result := (originalCoreCircleTrace_represents parameters first radius).add
    (originalCoreCircleTrace_represents parameters second radius)
    (originalCoreCircle_continuous parameters first radius) (originalCoreCircle_continuous parameters second radius)
  have equal : originalCoreCircle parameters (first+second) radius = (fun angles => originalCoreCircle parameters first radius angles+originalCoreCircle parameters second radius angles) := by
    funext angles
    exact coreValue_add _ _ _ _
  rw [equal]
  exact result

theorem originalCoreCircleTrace_sub {dimension : ℕ} (parameters : PhaseParameters)
    (first second : ACore parameters dimension) (radius : RadialPoint) :
    originalCoreCircleTrace parameters (first-second) radius =
      originalCoreCircleTrace parameters first radius-originalCoreCircleTrace parameters second radius := by
  apply (originalCoreCircleTrace_represents parameters (first-second) radius).unique
  have result := (originalCoreCircleTrace_represents parameters first radius).sub
    (originalCoreCircleTrace_represents parameters second radius)
    (originalCoreCircle_continuous parameters first radius) (originalCoreCircle_continuous parameters second radius)
  have equal : originalCoreCircle parameters (first-second) radius = (fun angles => originalCoreCircle parameters first radius angles-originalCoreCircle parameters second radius angles) := by
    funext angles
    exact coreValue_subtract _ _ _ _
  rw [equal]
  exact result

theorem originalTangentialFrame_dot (parameters : PhaseParameters) (length epsilon : ℝ)
    (base field : ACore parameters 3) (radius : RadialPoint) (angles : ℝ × ℝ) :
    (radius.val : ℂ) • originalPolarTangentialValue
      (WithLp.toLp 2 ((originalPhysicalFrameMatrix parameters length epsilon base angles.2
        (polarClosedPoint radius.val angles.1 radius.property.1 radius.property.2)).transpose.mulVec
        (originalCoreCircle parameters field radius angles))) angles.1 =
    originalCoreCircle parameters (dotOperation parameters (rotationCore parameters (planarReferenceCore parameters+base)) field) radius angles := by
  apply PiLp.ext
  intro row
  fin_cases row
  change _ = coreValue (dotOperation parameters (rotationCore parameters (planarReferenceCore parameters+base)) field) _ _ 0
  rw [coreValue_dotOperation,originalCore_rotation_value]
  simp only [Grad.NonlinearQuotient.complexDot,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
  simp_rw [originalTotalFirstDerivative_frame parameters length epsilon base]
  simp [originalPolarTangentialValue,matrixUnit_apply,operatorBasis,Matrix.mulVec,dotProduct,
    Matrix.transpose_apply,Fin.sum_univ_succ,originalCoreCircle,Grad.SourceCollarDivision.polarClosedPoint,polarPlane,
    Grad.BoundaryTrace.collarPlane]
  ring

end Grad.OriginalKernelRetainedDecay
