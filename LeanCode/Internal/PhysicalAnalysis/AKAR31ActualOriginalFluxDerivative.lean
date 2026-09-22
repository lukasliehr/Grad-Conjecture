import AKAR30PhysicalFluxRepresentation
import AKAR28ActualKernelXiIdentity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.FinitePhysicalJetLift
open Grad.SourceCollar Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.SourceCollarFullSource

def originalCircleFlux (parameters : PhaseParameters) (coefficients : AxisCircleCoefficients)
    (radius : RadialPoint) (vector : CellL2 3) (xi : CellL2 1) : CellL2 1 :=
  hilbertMeanFree parameters (coefficients.C vector+coefficients.kappa ((radius.val : ℂ)⁻¹ • xi))

def originalCircleFluxRotation (coefficients : AxisCircleCoefficients)
    (radius : RadialPoint) (vector rotated : CellL2 3) (xi rotatedXi : CellL2 1) : CellL2 1 :=
  (coefficients.RC vector+coefficients.C rotated)+
    (coefficients.Rkappa ((radius.val : ℂ)⁻¹ • xi)+coefficients.kappa ((radius.val : ℂ)⁻¹ • rotatedXi))

theorem originalCircleFlux_rotation (parameters : PhaseParameters) (primitives : AxisCirclePrimitives)
    (derivatives : primitives.HasDerivatives) (radius : RadialPoint)
    (vector rotated : CellL2 3) (xi rotatedXi : CellL2 1)
    (vectorRotation : OriginalCircleRotation vector rotated) (xiRotation : OriginalCircleRotation xi rotatedXi) :
    OriginalCircleRotation (originalCircleFlux parameters (primitives.coefficients parameters) radius vector xi)
      (originalCircleFluxRotation (primitives.coefficients parameters) radius vector rotated xi rotatedXi) :=
  ((derivatives.C parameters vector rotated vectorRotation).add
    (derivatives.kappa parameters _ _ (xiRotation.smul (radius.val : ℂ)⁻¹))).meanFree

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 8 ≤ originalCoefficientLowRadius parameters length)
    (radius : RadialPoint)

def originalKernelPhysicalP (total vector : ACore parameters 3) (scalar : ACore parameters 1) : CellL2 1 :=
  originalCircleFlux parameters (originalAxisCircleCoefficients parameters length rho epsilon base small radius) radius
    (originalCoreCircleTrace parameters vector radius) (originalCoreCircleTrace parameters (originalKernelXi total vector scalar) radius)

def originalKernelPhysicalX (total vector : ACore parameters 3) (scalar : ACore parameters 1) : CellL2 1 :=
  originalCircleFluxRotation (originalAxisCircleCoefficients parameters length rho epsilon base small radius) radius
    (originalCoreCircleTrace parameters vector radius) (originalCoreCircleTrace parameters (rotationCore parameters vector) radius)
    (originalCoreCircleTrace parameters (originalKernelXi total vector scalar) radius)
    (originalCoreCircleTrace parameters (rotationCore parameters (originalKernelXi total vector scalar)) radius)

/-- This is the actual p=P(C U+kappa xi/r), with the original D and B
families acting by literal physical multiplication. -/
theorem originalKernelPhysicalP_represents (total vector : ACore parameters 3) (scalar : ACore parameters 1) :
    OriginalCircleRepresents parameters radius (originalKernelPhysicalP parameters length rho epsilon base small radius total vector scalar)
      (removePolarMean (originalPhysicalRawFlux parameters length epsilon base radius
        (originalCoreCircle parameters vector radius) (originalCoreCircle parameters (originalKernelXi total vector scalar) radius))) :=
  (originalPhysicalRawFlux_represents parameters length rho epsilon base small radius _ _ _ _
    (originalCoreCircle_continuous parameters vector radius) (originalCoreCircle_continuous parameters _ radius)
    (originalCoreCircleTrace_represents parameters vector radius) (originalCoreCircleTrace_represents parameters _ radius)).meanFree
    (originalPhysicalRawFlux_continuous parameters length rho epsilon base small radius _ _
      (originalCoreCircle_continuous parameters vector radius) (originalCoreCircle_continuous parameters _ radius))

/-- Exact x=Rp for the same physical flux, with no completed annular-domain
membership assumption. -/
theorem originalKernelPhysicalX_is_rotation (total vector : ACore parameters 3) (scalar : ACore parameters 1) :
    OriginalCircleRotation (originalKernelPhysicalP parameters length rho epsilon base small radius total vector scalar)
      (originalKernelPhysicalX parameters length rho epsilon base small radius total vector scalar) :=
  originalCircleFlux_rotation parameters _
    (originalAxisCirclePrimitives_hasDerivatives parameters length rho epsilon base small radius) radius _ _ _ _
    (originalCoreCircleTrace_rotation parameters vector radius) (originalCoreCircleTrace_rotation parameters _ radius)

end Grad.OriginalKernelRetainedDecay
