import AKAR6FixedPolarCircleActions
import AKAR8LiteralCofactorCovector

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.SourceBoundaryTrace Grad.SourceCollarDivision
open Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.PhaseAlgebra Grad.BoundaryLift
open Grad.SourceCollarCoefficients Grad.ActualPhysicalField Grad.SourceCollar
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Envelope

structure AxisCirclePrimitives where
  frameTranspose : CellL2 3 →L[ℂ] CellL2 3
  rotationFrameTranspose : CellL2 3 →L[ℂ] CellL2 3
  covector : CellL2 3 →L[ℂ] CellL2 3
  rotationCovector : CellL2 3 →L[ℂ] CellL2 3
  cofactor : CellL2 3 →L[ℂ] CellL2 3
  rotationCofactor : CellL2 3 →L[ℂ] CellL2 3

structure AxisCircleCoefficients where
  c : CellL2 3 →L[ℂ] CellL2 1
  d : CellL2 3 →L[ℂ] CellL2 1
  C : CellL2 3 →L[ℂ] CellL2 1
  RC : CellL2 3 →L[ℂ] CellL2 1
  kappa : CellL2 1 →L[ℂ] CellL2 1
  Rkappa : CellL2 1 →L[ℂ] CellL2 1

/-- The literal polar formulas use R e_r=e_theta and R e_theta=-e_r. -/
def AxisCirclePrimitives.coefficients (primitives : AxisCirclePrimitives) (parameters : PhaseParameters) : AxisCircleCoefficients where
  c := (originalCircleTangentialRow parameters).comp primitives.frameTranspose
  d := (originalCircleTangentialRow parameters).comp primitives.rotationFrameTranspose -
    (originalCircleRadialRow parameters).comp primitives.frameTranspose
  C := (originalCircleRadialRow parameters).comp primitives.covector
  RC := (originalCircleTangentialRow parameters).comp primitives.covector +
    (originalCircleRadialRow parameters).comp primitives.rotationCovector
  kappa := (originalCircleTangentialRow parameters).comp (primitives.cofactor.comp (originalCircleRadialColumn parameters))
  Rkappa := -((originalCircleRadialRow parameters).comp (primitives.cofactor.comp (originalCircleRadialColumn parameters))) +
    (originalCircleTangentialRow parameters).comp (primitives.rotationCofactor.comp (originalCircleRadialColumn parameters)) +
    (originalCircleTangentialRow parameters).comp (primitives.cofactor.comp (originalCircleTangentialColumn parameters))

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 8 ≤ originalCoefficientLowRadius parameters length)
    (radius : RadialPoint)

/-- All six inputs are the actual original coefficient families on the same circle. -/
def originalAxisCirclePrimitives : AxisCirclePrimitives :=
  let low := (originalAxis_primitive_margin parameters length rho epsilon base small).1
  let f := (originalTransposeFrameFamily_estimate parameters length rho epsilon base low).actualCoherent
  let d := (originalCofactorCovectorFamily_estimate parameters length rho epsilon base low).actualCoherent
  let b := (originalCofactorFamily_estimate parameters length rho epsilon base low).actualCoherent
  { frameTranspose := originalCircleFamilyAction parameters (originalTransposeFrameFamily parameters length epsilon base) f radius
    rotationFrameTranspose := originalCircleFamilyAngularAction parameters (originalTransposeFrameFamily parameters length epsilon base) f radius
    covector := originalCircleFamilyAction parameters (originalCofactorCovectorFamily parameters length epsilon base) d radius
    rotationCovector := originalCircleFamilyAngularAction parameters (originalCofactorCovectorFamily parameters length epsilon base) d radius
    cofactor := originalCircleFamilyAction parameters (originalCofactorFamily parameters length epsilon base) b radius
    rotationCofactor := originalCircleFamilyAngularAction parameters (originalCofactorFamily parameters length epsilon base) b radius }

def originalAxisCircleCoefficients : AxisCircleCoefficients :=
  (originalAxisCirclePrimitives parameters length rho epsilon base small radius).coefficients parameters

end Grad.OriginalKernelRetainedDecay
