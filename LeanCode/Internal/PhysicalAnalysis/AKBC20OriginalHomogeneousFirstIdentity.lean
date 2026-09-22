import AKBC19OriginalDomainAnnularGauges

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.FinitePhysicalJetLift
open Grad.SourceCollar Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularReconstruction Grad.OriginalKernelRetainedDecay

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 8≤originalCoefficientLowRadius parameters length)
    (radius : RadialPoint)

def originalCircleTangentialRotation (vector : ACore parameters 3) :=
  (originalAxisCircleCoefficients parameters length rho epsilon base small radius).d
    (originalCoreCircleTrace parameters vector radius)+
  (originalAxisCircleCoefficients parameters length rho epsilon base small radius).c
    (originalCoreCircleTrace parameters (rotationCore parameters vector) radius)

theorem originalCircleTangentialRotation_actual (vector : ACore parameters 3) :
    OriginalCircleRotation
      ((originalAxisCircleCoefficients parameters length rho epsilon base small radius).c
        (originalCoreCircleTrace parameters vector radius))
      (originalCircleTangentialRotation parameters length rho epsilon base small radius vector) :=
  (originalAxisCirclePrimitives_hasDerivatives parameters length rho epsilon base small radius).c parameters
    (originalCoreCircleTrace parameters vector radius) (originalCoreCircleTrace parameters (rotationCore parameters vector) radius)
    (originalCoreCircleTrace_rotation parameters vector radius)

/-- The original homogeneous quotient derivative supplies the literal first
normalized force identity on its own original-width circle field. All four
terms use the same actual F_C and its genuine angular derivative. -/
theorem originalHomogeneous_firstCircleIdentity (positive : 0<radius.val) (state : QuotientState parameters)
    (sameBase : state.2.1=planarReferenceCore parameters+base) (vector : ACore parameters 3) (scalar : ACore parameters 1)
    (homogeneous : quotientRowsDerivative parameters length 1 state ![(0,vector,scalar)]=0) :
    (radius.val : ℂ)⁻¹ • originalCoreCircleTrace parameters (rotationCore parameters (originalKernelXi state.2.1 vector scalar)) radius -
      originalCircleTangentialRotation parameters length rho epsilon base small radius vector -
      (2 : ℂ) • originalCircleRadialRow parameters
        ((originalAxisCirclePrimitives parameters length rho epsilon base small radius).frameTranspose
          (originalCoreCircleTrace parameters vector radius)) +
      (2 : ℂ) • originalCircleTangentialRow parameters
        ((originalAxisCirclePrimitives parameters length rho epsilon base small radius).rotationFrameTranspose
          (originalCoreCircleTrace parameters vector radius))=0 := by
  rw [originalKernelXi_circle_rotation parameters length rho epsilon base small radius state sameBase vector scalar homogeneous,
    inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr positive.ne')]
  simp only [originalCircleTangentialRotation,originalAxisCircleCoefficients,AxisCirclePrimitives.coefficients,
    ContinuousLinearMap.comp_apply,sub_apply]
  module

end Grad.OriginalKernelCovariantRecovery
