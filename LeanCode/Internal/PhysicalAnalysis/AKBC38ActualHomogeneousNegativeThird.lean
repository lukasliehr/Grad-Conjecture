import AKBC37SameOriginalNegativeAxialTrace

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

/-- The exact original fourth quotient equation supplies AHS's third force
row on the same full negative trace, including its original P and L^-1. -/
theorem originalHomogeneous_negativeThird (physicalState : QuotientState parameters)
    (sameBase : physicalState.2.1=planarReferenceCore parameters+state.val.data.field)
    (sameEpsilon : physicalState.1=(state.val.data.epsilon : ℂ)) (scalar : ACore parameters 1)
    (homogeneous : quotientRowsDerivative parameters length 1 physicalState ![(0,vector,scalar)]=0) :
    let curves := originalPolarCovariantCurves parameters length state.val.data.rho state.val.data.epsilon state.val.data.field state.val.low
      lower positive bounded vector;
    let xi := originalCoreLowCurves parameters lower positive bounded (originalKernelXi physicalState.2.1 vector scalar);
    forceCoordinateTrace _ 0 0 2 (originalCurveNegativeRotation curves radius)+
      forceMeanFreeTrace _ 0 0 (fullNegativeKernelAction _ 0 0
        (radialForceKernel parameters length compact state.val (tupleRadius lower positive radius) 1 0)
        (originalCurveNegativeTrace curves radius))-
      (length : ℂ)⁻¹ • originalCurveNegativeAxial xi radius=0 := by
  let r := tupleRadius lower positive radius
  let cart := originalCartesianCovariantCurves parameters length state.val.data.rho state.val.data.epsilon state.val.data.field state.val.low
    lower positive bounded vector
  let curves := originalPolarFromCartesianCurves cart
  let xi := originalCoreLowCurves parameters lower positive bounded (originalKernelXi physicalState.2.1 vector scalar)
  let a2 := valueMapCore parameters (matrixUnit (0 : Fin 1) (2 : Fin 3))
    (originalCovariantCore parameters length state.val.data.epsilon state.val.data.field vector false)
  let forceCore := (-2 : ℂ) • valueMapCore parameters (matrixUnit (0 : Fin 1) (2 : Fin 3))
    (originalCovariantCore parameters length state.val.data.epsilon state.val.data.field vector true)
  let primitives := originalAxisCirclePrimitives parameters length state.val.data.rho state.val.data.epsilon state.val.data.field small r
  have represented := originalCartesianCovariantCircle_represents parameters length state.val.data.rho state.val.data.epsilon
    state.val.data.field state.val.low lower positive bounded vector radius
  have axial : OriginalNegativeCircle parameters r
      (forceCoordinateTrace _ 0 0 2 (originalCurveNegativeTrace curves radius)) (originalCoreCircleTrace parameters a2 r) := by
    have original := originalPolarNegative_axial cart bounded radius _ represented
    change OriginalNegativeCircle parameters r _
      (originalCircleMatrix parameters (matrixUnit (0 : Fin 1) (2 : Fin 3))
        (primitives.frameTranspose (originalCoreCircleTrace parameters vector r))) at original
    rw [originalFrameCircle_sameCore parameters length state.val.data.rho state.val.data.epsilon nonzero state.val.data.field small r vector,
      ← originalCoreCircleTrace_valueMap] at original
    exact original
  have rotation : IsAngularDerivative _ 0 0
      (forceCoordinateTrace _ 0 0 2 (originalCurveNegativeTrace curves radius))
      (forceCoordinateTrace _ 0 0 2 (originalCurveNegativeRotation curves radius)) :=
    (originalCurveNegativeRotation_derivative curves bounded radius).constantMatrix (matrixUnit (0 : Fin 1) (2 : Fin 3))
  have rotated := axial.rotation rotation (originalCoreCircleTrace_rotation parameters a2 r)
  have scalarTrace : OriginalNegativeCircle parameters r (originalCurveNegativeTrace xi radius)
      (originalCoreCircleTrace parameters (originalKernelXi physicalState.2.1 vector scalar) r) :=
    originalCoreNegative_circle parameters lower positive bounded (originalKernelXi physicalState.2.1 vector scalar) radius xi
      (originalCoreLowCurves_fullField parameters lower positive bounded _ radius.val radius.property)
  have scalarAxial := originalCoreNegative_axial xi bounded radius _ scalarTrace
  have force : OriginalNegativeCircle parameters r
      (fullNegativeKernelAction _ 0 0 (radialForceKernel parameters length compact state.val r 1 0)
        (originalCurveNegativeTrace curves radius)) (originalCoreCircleTrace parameters forceCore r) := by
    have original := originalForceNegative_circle parameters length compact nonzero state lower positive bounded vector radius 1
    change OriginalNegativeCircle parameters r _
      ((-2 : ℂ) • originalCircleMatrix parameters (matrixUnit (0 : Fin 1) (2 : Fin 3))
        (originalCoreCircleTrace parameters (originalCovariantCore parameters length state.val.data.epsilon state.val.data.field vector true) r)) at original
    rw [← originalCoreCircleTrace_valueMap,← originalCoreCircleTrace_smul] at original
    exact original
  have projected := force.meanFree
  rw [← originalCoreCircleTrace_meanFree] at projected
  apply ((rotated.add projected).sub (scalarAxial.smul (length : ℂ)⁻¹)).eq_zero
  rw [← originalCoreCircleTrace_smul,← originalCoreCircleTrace_add,← originalCoreCircleTrace_sub]
  rw [originalHomogeneous_axialCovariantCore parameters length state.val.data.epsilon state.val.data.field vector scalar
    physicalState sameBase sameEpsilon homogeneous,originalCoreCircleTrace_zero]

end Grad.OriginalKernelCovariantRecovery
