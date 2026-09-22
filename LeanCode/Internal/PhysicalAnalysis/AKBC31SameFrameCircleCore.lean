import AKBC30OriginalCovariantCoreProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.OriginalKernelRetainedDecay Grad.NonlinearQuotientBounds
open Grad.SourceCollar Grad.ActualPhysicalField Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (nonzero : length≠0)
    (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 8≤originalCoefficientLowRadius parameters length)
    (radius : RadialPoint) (vector : ACore parameters 3)

include nonzero

theorem originalFrameCircle_sameCore :
    (originalAxisCirclePrimitives parameters length rho epsilon base small radius).frameTranspose
      (originalCoreCircleTrace parameters vector radius)=
      originalCoreCircleTrace parameters (originalCovariantCore parameters length epsilon base vector false) radius := by
  let low := (originalAxis_primitive_margin parameters length rho epsilon base small).1
  have represented := (originalCoreCircleTrace_represents parameters vector radius).matrix_literal parameters
    (originalTransposeFrameFamily parameters length epsilon base)
    (originalTransposeFrameFamily_estimate parameters length rho epsilon base low).actualCoherent
    radius (originalCoreCircleTrace parameters vector radius) (originalCoreCircle parameters vector radius)
    (originalCoreCircle_continuous parameters vector radius)
  apply OriginalCircleRepresents.unique ?_ (originalCoreCircleTrace_represents parameters _ radius)
  intro mode
  refine (represented mode).trans ?_
  congr 1
  funext angles
  rw [originalTransposeFrameFamily_matrix parameters length rho epsilon base low]
  exact (originalCovariantCore_value parameters length epsilon nonzero base vector _ _).symm

theorem originalRotationFrameCircle_sameCore :
    (originalAxisCirclePrimitives parameters length rho epsilon base small radius).rotationFrameTranspose
      (originalCoreCircleTrace parameters vector radius)=
      originalCoreCircleTrace parameters (originalCovariantCore parameters length epsilon base vector true) radius := by
  have derivative := (originalAxisCirclePrimitives_hasDerivatives parameters length rho epsilon base small radius).frame
    (originalCoreCircleTrace parameters vector radius)
    (originalCoreCircleTrace parameters (rotationCore parameters vector) radius)
    (originalCoreCircleTrace_rotation parameters vector radius)
  rw [originalFrameCircle_sameCore parameters length rho epsilon nonzero base small radius vector,
    originalFrameCircle_sameCore parameters length rho epsilon nonzero base small radius (rotationCore parameters vector)] at derivative
  have original := originalCoreCircleTrace_rotation parameters
    (originalCovariantCore parameters length epsilon base vector false) radius
  rw [originalCovariantCore_rotation,originalCoreCircleTrace_add] at original
  exact add_right_cancel (derivative.unique original)

end Grad.OriginalKernelCovariantRecovery
