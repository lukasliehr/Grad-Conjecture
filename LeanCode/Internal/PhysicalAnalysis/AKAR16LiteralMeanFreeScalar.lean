import AKAR15OriginalRotationProductRule

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.NonlinearRange Grad.FlatSourceProjection Grad.QuotientProjection
open Grad.FinitePhysicalJetLift

/-- The original scalar retained coordinate, before any annular completion. -/
def originalKernelXi {parameters : PhaseParameters} (base vector : ACore parameters 3) (scalar : ACore parameters 1) :
    ACore parameters 1 :=
  removeAngularCore parameters (scalar-dotOperation parameters (rotationCore parameters base) vector)

theorem originalKernelXi_mean {parameters : PhaseParameters} (base vector : ACore parameters 3) (scalar : ACore parameters 1) :
    angularCore parameters 0 (originalKernelXi base vector scalar) = 0 := angularCore_removeAngularCore _

/-- The genuine first-row scalar identity follows from the original quotient
kernel and the exact product rule, retaining the same mean-free xi. -/
theorem originalKernelXi_rotation (parameters : PhaseParameters) (length : ℝ)
    (base : QuotientState parameters) (vector : ACore parameters 3) (scalar : ACore parameters 1)
    (homogeneous : quotientRowsDerivative parameters length 1 base ![(0,vector,scalar)] = 0) :
    rotationCore parameters (originalKernelXi base.2.1 vector scalar) =
      dotOperation parameters (rotationCore parameters base.2.1) (rotationCore parameters vector) -
        dotOperation parameters (rotationCore parameters (rotationCore parameters base.2.1)) vector := by
  rw [originalKernelXi,rotationCore_removeAngular,map_sub,originalDot_rotation,
    originalHomogeneous_first_row parameters length base vector scalar homogeneous]
  module

end Grad.OriginalKernelRetainedDecay
