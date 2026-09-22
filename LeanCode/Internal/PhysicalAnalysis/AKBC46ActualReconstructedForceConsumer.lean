import AKBC45ActualHomogeneousCovariantRecovery

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open Set
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.SourceCollarFullSource Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.OriginalKernelGraphRestriction Grad.OriginalKernelRetainedDecay Grad.Constraints Grad.Cor18
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.NonlinearQuotientBounds Grad.PhysicalCoordinates Grad.SourceCollar Grad.FinitePhysicalJetLift

variable (parameters : PhaseParameters) (compact : ℝ) (nonzero : parameters.length≠0)
    (state : RetainedInverseState parameters parameters.length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤
      originalCoefficientLowRadius parameters parameters.length)
    (insideSeed : originalCoefficientSeed parameters compact state.val.val∈Seed.parameterDomain)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (physicalState : QuotientState parameters)
    (sameBase : physicalState.2.1=planarReferenceCore parameters+state.val.val.field)
    (sameEpsilon : physicalState.1=(state.val.val.epsilon : ℂ))
    (vector : ACore parameters 3) (scalar : ACore parameters 1)
    (constrained : VectorConstraints parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed
      (toPhysicalCore parameters vector))
    (homogeneous : quotientRowsDerivative parameters parameters.length 1 physicalState ![(0,vector,scalar)]=0)
    (radius : Icc lower (1 : ℝ))

include nonzero sameBase sameEpsilon constrained homogeneous

/-- Immediate derivative consumer: the immutable reconstructed Ra is the
actual angular derivative of the same original physical covariant. -/
theorem originalHomogeneous_rotatedCovariantRecovery :
    tupleRotatedCovariantTrace parameters parameters.length compact lower positive state
      (originalKernelSmoothTuple parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
        lower positive bounded physicalState.2.1 vector scalar) radius=
    originalCurveNegativeRotation
      (originalPolarCovariantCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
        lower positive bounded vector) radius := by
  apply NegativeTrace.ext_coefficient _ 0 0
  intro mode
  rw [tupleCovariantTrace_derivative parameters parameters.length compact lower positive state _ radius mode,
    originalCurveNegativeRotation_derivative _ bounded radius mode,
    originalHomogeneous_covariantRecovery parameters compact nonzero state small insideSeed lower positive bounded physicalState
      sameBase sameEpsilon vector scalar constrained homogeneous radius]

/-- The computed original first residual uses the SAME physical a and Ra;
no retained force or reconstructed field is introduced as an assumption. -/
theorem originalHomogeneous_firstRowRecovery :
    let curves := originalPolarCovariantCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
      lower positive bounded vector
    tupleFirstRowTrace parameters parameters.length compact lower positive state
      (originalKernelSmoothTuple parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
        lower positive bounded physicalState.2.1 vector scalar) radius=
      forceCoordinateTrace _ 0 0 0 (originalCurveNegativeRotation curves radius)-
      fullNegativeKernelAction _ 0 0
        (radialRetainedForceKernel parameters parameters.length compact state.val.val (tupleRadius lower positive radius))
        (originalCurveNegativeTrace curves radius) := by
  dsimp only
  rw [tupleFirstRowTrace,
    originalHomogeneous_rotatedCovariantRecovery parameters compact nonzero state small insideSeed lower positive bounded physicalState
      sameBase sameEpsilon vector scalar constrained homogeneous radius,
    ← originalHomogeneous_covariantRecovery parameters compact nonzero state small insideSeed lower positive bounded physicalState
      sameBase sameEpsilon vector scalar constrained homogeneous radius]

end Grad.OriginalKernelCovariantRecovery
