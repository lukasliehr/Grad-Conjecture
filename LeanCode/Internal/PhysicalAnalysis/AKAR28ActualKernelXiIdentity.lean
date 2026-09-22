import AKAR27LiteralCAndD

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.FinitePhysicalJetLift
open Grad.SourceCollar Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularReconstruction

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 8 ≤ originalCoefficientLowRadius parameters length)
    (radius : RadialPoint)

theorem originalKernelXi_circle_rotation (state : QuotientState parameters)
    (sameBase : state.2.1=planarReferenceCore parameters+base) (vector : ACore parameters 3) (scalar : ACore parameters 1)
    (homogeneous : quotientRowsDerivative parameters length 1 state ![(0,vector,scalar)] = 0) :
    originalCoreCircleTrace parameters (rotationCore parameters (originalKernelXi state.2.1 vector scalar)) radius =
      (radius.val : ℂ) •
        ((originalAxisCircleCoefficients parameters length rho epsilon base small radius).c
          (originalCoreCircleTrace parameters (rotationCore parameters vector) radius) -
        (originalAxisCircleCoefficients parameters length rho epsilon base small radius).d
          (originalCoreCircleTrace parameters vector radius)) := by
  rw [originalKernelXi_rotation parameters length state vector scalar homogeneous,sameBase,originalCoreCircleTrace_sub,
    originalCircle_c_literal parameters length rho epsilon base small radius,
    originalCircle_d_literal parameters length rho epsilon base small radius,smul_sub]

theorem originalKernelXi_circle_formula (state : QuotientState parameters)
    (sameBase : state.2.1=planarReferenceCore parameters+base) (vector : ACore parameters 3) (scalar : ACore parameters 1)
    (homogeneous : quotientRowsDerivative parameters length 1 state ![(0,vector,scalar)] = 0) :
    originalCoreCircleTrace parameters (originalKernelXi state.2.1 vector scalar) radius =
      (radius.val : ℂ) • originalCircleAngularInverse parameters 1
        ((originalAxisCircleCoefficients parameters length rho epsilon base small radius).c
          (originalCoreCircleTrace parameters (rotationCore parameters vector) radius) -
        (originalAxisCircleCoefficients parameters length rho epsilon base small radius).d
          (originalCoreCircleTrace parameters vector radius)) := by
  rw [originalKernelXi_circle_primitive,originalKernelXi_circle_rotation parameters length rho epsilon base small radius
    state sameBase vector scalar homogeneous,map_smul]

end Grad.OriginalKernelRetainedDecay
