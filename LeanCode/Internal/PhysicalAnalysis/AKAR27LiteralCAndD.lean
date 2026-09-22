import AKAR25PhysicalTangentialFrame
import AKAR26SixActualAngularDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.FinitePhysicalJetLift
open Grad.SourceCollar Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularReconstruction Grad.ActualSmoothPhysicalField

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 8 ≤ originalCoefficientLowRadius parameters length)
    (radius : RadialPoint)

theorem originalCircle_c_literal (field : ACore parameters 3) :
    originalCoreCircleTrace parameters (dotOperation parameters (rotationCore parameters (planarReferenceCore parameters+base)) field) radius =
      (radius.val : ℂ) • (originalAxisCircleCoefficients parameters length rho epsilon base small radius).c
        (originalCoreCircleTrace parameters field radius) := by
  let family := originalTransposeFrameFamily parameters length epsilon base
  let low := (originalAxis_primitive_margin parameters length rho epsilon base small).1
  let coherent := (originalTransposeFrameFamily_estimate parameters length rho epsilon base low).actualCoherent
  let source := originalCoreCircle parameters field radius
  have represented := (originalCoreCircleTrace_represents parameters field radius).matrix parameters family coherent radius
    (originalCoreCircleTrace parameters field radius) source (originalCoreCircle_continuous parameters field radius)
  have continuous := physicalMatrixProduct_continuous parameters family coherent radius.val radius.property.1 radius.property.2 source
    (originalCoreCircle_continuous parameters field radius)
  have row := (represented.tangential continuous).smul (radius.val : ℂ)
  have equality : (fun angles => (radius.val : ℂ) • originalPolarTangentialValue
      (physicalMatrixProduct parameters family radius.val radius.property.1 radius.property.2 source angles) angles.1) =
      originalCoreCircle parameters (dotOperation parameters (rotationCore parameters (planarReferenceCore parameters+base)) field) radius := by
    funext angles
    rw [physicalMatrixProduct_apply]
    change (radius.val : ℂ) • originalPolarTangentialValue
      (WithLp.toLp 2 ((familyMatrix (originalTransposeFrameFamily parameters length epsilon base) 0 angles.2
        (Grad.SourceCollarDivision.polarClosedPoint radius.val angles.1 radius.property.1 radius.property.2)).mulVec (source angles))) angles.1 = _
    rw [originalTransposeFrameFamily_matrix parameters length rho epsilon base low]
    exact originalTangentialFrame_dot parameters length epsilon base field radius angles
  rw [equality] at row
  exact (originalCoreCircleTrace_represents parameters _ radius).unique row

theorem originalCircle_d_literal (field : ACore parameters 3) :
    originalCoreCircleTrace parameters
      (dotOperation parameters (rotationCore parameters (rotationCore parameters (planarReferenceCore parameters+base))) field) radius =
      (radius.val : ℂ) • (originalAxisCircleCoefficients parameters length rho epsilon base small radius).d
        (originalCoreCircleTrace parameters field radius) := by
  have derivative := (originalAxisCirclePrimitives_hasDerivatives parameters length rho epsilon base small radius).c parameters
    (originalCoreCircleTrace parameters field radius) (originalCoreCircleTrace parameters (rotationCore parameters field) radius)
    (originalCoreCircleTrace_rotation parameters field radius)
  have weighted := derivative.smul (radius.val : ℂ)
  change OriginalCircleRotation
    ((radius.val : ℂ) • (originalAxisCircleCoefficients parameters length rho epsilon base small radius).c (originalCoreCircleTrace parameters field radius))
    ((radius.val : ℂ) • ((originalAxisCircleCoefficients parameters length rho epsilon base small radius).d (originalCoreCircleTrace parameters field radius)+
      (originalAxisCircleCoefficients parameters length rho epsilon base small radius).c (originalCoreCircleTrace parameters (rotationCore parameters field) radius))) at weighted
  rw [← originalCircle_c_literal parameters length rho epsilon base small radius field] at weighted
  have equality := (originalCoreCircleTrace_rotation parameters
    (dotOperation parameters (rotationCore parameters (planarReferenceCore parameters+base)) field) radius).unique weighted
  rw [originalDot_rotation,originalCoreCircleTrace_add,
    originalCircle_c_literal parameters length rho epsilon base small radius (rotationCore parameters field),smul_add] at equality
  exact add_right_cancel equality

end Grad.OriginalKernelRetainedDecay
