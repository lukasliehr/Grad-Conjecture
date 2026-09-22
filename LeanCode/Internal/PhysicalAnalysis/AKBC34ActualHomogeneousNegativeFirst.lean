import AKBC33NegativeCircleLinearAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.SourceCollarFullSource
open Grad.AnnularReconstruction Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.BoundaryKernelAction Grad.OriginalKernelRetainedDecay Grad.OriginalKernelGraphRestriction
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.SourceCollar Grad.ActualPhysicalField Grad.NonlinearQuotientBounds Grad.FinitePhysicalJetLift

variable (parameters : PhaseParameters) (length compact : ℝ) (nonzero : length≠0)
    (state : AnnularReconstructionState parameters length compact)
    (small : physicalBudget parameters state.val.data.field state.val.data.rho state.val.data.epsilon 8≤
      originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (vector : ACore parameters 3)
    (radius : Icc lower (1 : ℝ))

include small nonzero

/-- The exact first normalized AHS force row follows from the original
physical homogeneous derivative for the SAME covariant and xi traces. -/
theorem originalHomogeneous_negativeFirst (physicalState : QuotientState parameters)
    (sameBase : physicalState.2.1=planarReferenceCore parameters+state.val.data.field)
    (scalar : ACore parameters 1)
    (homogeneous : quotientRowsDerivative parameters length 1 physicalState ![(0,vector,scalar)]=0) :
    let curves := originalPolarCovariantCurves parameters length state.val.data.rho state.val.data.epsilon state.val.data.field state.val.low
      lower positive bounded vector;
    let xi := originalCoreLowCurves parameters lower positive bounded (originalKernelXi physicalState.2.1 vector scalar);
    -forceCoordinateTrace _ 0 0 1 (originalCurveNegativeRotation curves radius)-
      (2 : ℂ) • forceCoordinateTrace _ 0 0 0 (originalCurveNegativeTrace curves radius)+
      fullNegativeKernelAction _ 0 0
        (radialForceKernel parameters length compact state.val (tupleRadius lower positive radius) 0 0)
        (originalCurveNegativeTrace curves radius)+
      (radius.val : ℂ)⁻¹ • originalCurveNegativeRotation xi radius=0 := by
  let r := tupleRadius lower positive radius
  let cart := originalCartesianCovariantCurves parameters length state.val.data.rho state.val.data.epsilon state.val.data.field state.val.low
    lower positive bounded vector
  let curves := originalPolarFromCartesianCurves cart
  let xi := originalCoreLowCurves parameters lower positive bounded (originalKernelXi physicalState.2.1 vector scalar)
  let primitives := originalAxisCirclePrimitives parameters length state.val.data.rho state.val.data.epsilon state.val.data.field small r
  let u := originalCoreCircleTrace parameters vector r
  have represented := originalCartesianCovariantCircle_represents parameters length state.val.data.rho state.val.data.epsilon
    state.val.data.field state.val.low lower positive bounded vector radius
  have radial : OriginalNegativeCircle parameters r
      (forceCoordinateTrace _ 0 0 0 (originalCurveNegativeTrace curves radius))
      (originalCircleRadialRow parameters (primitives.frameTranspose u)) :=
    originalPolarNegative_radial cart bounded radius _ represented
  have tangential : OriginalNegativeCircle parameters r
      (forceCoordinateTrace _ 0 0 1 (originalCurveNegativeTrace curves radius))
      ((originalAxisCircleCoefficients parameters length state.val.data.rho state.val.data.epsilon state.val.data.field small r).c u) :=
    originalPolarNegative_tangential cart bounded radius _ represented
  have rotation : IsAngularDerivative _ 0 0
      (forceCoordinateTrace _ 0 0 1 (originalCurveNegativeTrace curves radius))
      (forceCoordinateTrace _ 0 0 1 (originalCurveNegativeRotation curves radius)) :=
    (originalCurveNegativeRotation_derivative curves bounded radius).constantMatrix (matrixUnit (0 : Fin 1) (1 : Fin 3))
  have rotated := tangential.rotation rotation
    (originalCircleTangentialRotation_actual parameters length state.val.data.rho state.val.data.epsilon state.val.data.field small r vector)
  have scalarTrace : OriginalNegativeCircle parameters r (originalCurveNegativeTrace xi radius)
      (originalCoreCircleTrace parameters (originalKernelXi physicalState.2.1 vector scalar) r) :=
    originalCoreNegative_circle parameters lower positive bounded (originalKernelXi physicalState.2.1 vector scalar) radius xi
      (originalCoreLowCurves_fullField parameters lower positive bounded _ radius.val radius.property)
  have scalarRotation := scalarTrace.rotation (originalCurveNegativeRotation_derivative xi bounded radius)
    (originalCoreCircleTrace_rotation parameters (originalKernelXi physicalState.2.1 vector scalar) r)
  have force : OriginalNegativeCircle parameters r
      (fullNegativeKernelAction _ 0 0 (radialForceKernel parameters length compact state.val r 0 0)
        (originalCurveNegativeTrace curves radius))
      ((2 : ℂ) • originalCircleTangentialRow parameters (primitives.rotationFrameTranspose u)) := by
    have original := originalForceNegative_circle parameters length compact nonzero state lower positive bounded vector radius 0
    change OriginalNegativeCircle parameters r _
      ((2 : ℂ) • originalCircleTangentialRow parameters
        (originalCoreCircleTrace parameters (originalCovariantCore parameters length state.val.data.epsilon state.val.data.field vector true) r)) at original
    rw [← originalRotationFrameCircle_sameCore parameters length state.val.data.rho state.val.data.epsilon nonzero
      state.val.data.field small r vector] at original
    exact original
  apply (((rotated.neg.sub (radial.smul 2)).add force).add (scalarRotation.smul (radius.val : ℂ)⁻¹)).eq_zero
  have actual := originalHomogeneous_firstCircleIdentity parameters length state.val.data.rho state.val.data.epsilon state.val.data.field small r
    (positive.trans_le radius.property.1) physicalState sameBase vector scalar homogeneous
  change (radius.val : ℂ)⁻¹ • _-_-(2 : ℂ) • _+(2 : ℂ) • _=0 at actual
  convert actual using 1
  abel

end Grad.OriginalKernelCovariantRecovery
