import AKBC44SameOriginalNormalizedInput

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

/-- The actual original constrained homogeneous field is exactly the
immutable seven-slot covariant reconstruction of its own p and xi. -/
theorem originalHomogeneous_covariantRecovery :
    originalCurveNegativeTrace
      (originalPolarCovariantCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
        lower positive bounded vector) radius=
    tupleCovariantTrace parameters parameters.length compact lower positive state
      (originalKernelSmoothTuple parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
        lower positive bounded physicalState.2.1 vector scalar) radius := by
  let r := tupleRadius lower positive radius
  let curves := originalPolarCovariantCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
    lower positive bounded vector
  let xi := originalCoreLowCurves parameters lower positive bounded (originalKernelXi physicalState.2.1 vector scalar)
  let pressure := (originalRawFluxCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded (originalVectorLowCurves parameters lower positive bounded vector) xi).2.meanFree
  let tuple := originalKernelSmoothTuple parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded physicalState.2.1 vector scalar
  let input := tupleNormalizedInput parameters lower positive tuple radius
  have sameInput : input=WithLp.toLp 2 ![originalCurveNegativeRotation pressure radius,
      (radius.val : ℂ)⁻¹ • originalCurveNegativeRotation xi radius,originalCurveNegativeAxial xi radius,
      (radius.val : ℂ)⁻¹ • originalCurveNegativeTrace xi radius,0,0,0] :=
    originalKernelTuple_normalizedInput parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
      lower positive bounded physicalState.2.1 vector scalar radius
  have rotation := originalCurveNegativeRotation_derivative curves bounded radius
  have second := originalCurveNegativeSecondRotation_derivative curves bounded radius
  have scalarRotation : IsAngularDerivative _ 0 0 (input 3) (input 1) :=
    radialNormalizedSevenInput_derivative parameters r 0 0 _ (tupleSevenInput_scalarDerivative parameters lower positive tuple radius)
  have scalarSecond : IsAngularDerivative _ 0 0 (input 1)
      ((radius.val : ℂ)⁻¹ • originalCurveNegativeSecondRotation xi radius) := by
    rw [sameInput]
    exact angularDerivative_smul_trace (originalCurveNegativeSecondRotation_derivative xi bounded radius) _
  have scalarMean : IsAngularMeanFree _ 0 0 (input 3) := by
    rw [sameInput]
    apply IsAngularMeanFree.smul
    rw [← tupleNegativeTrace_sameCurves xi bounded tuple 1 rfl radius]
    exact tupleNegativeTrace_meanFree parameters lower positive tuple radius 1 (by decide)
  have sourceRotation : IsAngularDerivative _ 0 0 (input 4) (input 5) :=
    tupleSevenInput_sourceDerivative parameters lower positive tuple radius
  have gauges := originalDomain_annularGauges parameters compact state.val.val insideSeed vector constrained lower positive bounded radius
  have first : -forceCoordinateTrace _ 0 0 1 (originalCurveNegativeRotation curves radius)-
      (2 : ℂ) • forceCoordinateTrace _ 0 0 0 (originalCurveNegativeTrace curves radius)+
      fullNegativeKernelAction _ 0 0 (radialForceKernel parameters parameters.length compact state.val.val r 0 0)
        (originalCurveNegativeTrace curves radius)+input 1=input 4 := by
    rw [sameInput]
    exact originalHomogeneous_negativeFirst parameters parameters.length compact nonzero state.val small lower positive bounded vector radius
      physicalState sameBase scalar homogeneous
  have third : forceCoordinateTrace _ 0 0 2 (originalCurveNegativeRotation curves radius)+
      forceMeanFreeTrace _ 0 0 (fullNegativeKernelAction _ 0 0
        (radialForceKernel parameters parameters.length compact state.val.val r 1 0) (originalCurveNegativeTrace curves radius))-
      (parameters.length : ℂ)⁻¹ • input 2=input 6 := by
    rw [sameInput]
    exact originalHomogeneous_negativeThird parameters parameters.length compact nonzero state.val small lower positive bounded vector radius
      physicalState sameBase sameEpsilon scalar homogeneous
  have preMass := originalCovariant_preMass parameters parameters.length compact state.val.val r state.val.firstSmall 0 0
    (originalCurveNegativeTrace curves radius) (originalCurveNegativeRotation curves radius) (originalCurveNegativeSecondRotation curves radius)
    input ((radius.val : ℂ)⁻¹ • originalCurveNegativeSecondRotation xi radius)
    rotation second scalarRotation scalarSecond scalarMean sourceRotation gauges first third
  have fluxRotation : IsAngularDerivative _ 0 0
      (radialCorrectedFluxTrace parameters parameters.length compact state.val.val r 0 0
        (originalCurveNegativeTrace curves radius) (input 3)) (input 0) := by
    rw [sameInput]
    change IsAngularDerivative _ 0 0
      (radialCorrectedFluxTrace parameters parameters.length compact state.val.val r 0 0
        (originalCurveNegativeTrace curves radius) ((radius.val : ℂ)⁻¹ • originalCurveNegativeTrace xi radius))
      (originalCurveNegativeRotation pressure radius)
    rw [originalCorrectedFlux_samePressure parameters parameters.length compact lower positive bounded state small vector xi radius]
    exact originalCurveNegativeRotation_derivative pressure bounded radius
  have recovered := originalCovariant_massRecovery parameters parameters.length compact state.val.val r state.val.property 0 0
    (originalCurveNegativeTrace curves radius) (forceCoordinateTrace _ 0 0 0 (originalCurveNegativeRotation curves radius)) input
    (rotation.constantMatrix (matrixUnit (0 : Fin 1) (0 : Fin 3))).meanFree scalarRotation preMass fluxRotation
  simpa only [tupleCovariantTrace,radialCovariantKernel,fullNegativeKernelAction_comp,ContinuousLinearMap.comp_apply,
    radialSevenSlotKernel_action,tupleNormalizedInput,curves,input,tuple,r] using recovered

end Grad.OriginalKernelCovariantRecovery
