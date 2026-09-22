import AKBU15ActualNegativeTraceZeroField

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Set Filter
open scoped Topology
namespace Grad.OriginalPhysicalKernelUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularIncomingIntegrability Grad.AnnularWeightedUniqueness
open Grad.OriginalKernelGraphRestriction Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelOuterUniqueness
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.NonlinearQuotientBounds Grad.FinitePhysicalJetLift Grad.PhysicalCoordinates Grad.Constraints Grad.Cor18
open Grad.ActualSmoothPhysicalField Grad.OriginalKernelRetainedDecay Grad.ActualPhysicalField Grad.SourceCollar
open Grad.AnnularOriginalSmoothCore Grad.AnnularOriginalCoreRealization Grad.BoundaryKernelAction Grad.SourceBoundaryTrace
open Grad.AnnularWeakExhaustion Grad.AnnularExhaustionEstimate Grad.ActualAnnularExhaustion Grad.AnnularRestriction

variable (parameters : PhaseParameters) (compact : ℝ) (lengthPositive : 0<parameters.length)
    (widthHalf : parameters.gamma≤1/2) (widthLength : parameters.gamma≤Real.sqrt 5/(6*parameters.length))
    (state : RetainedInverseState parameters parameters.length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤originalCoefficientLowRadius parameters parameters.length)
    (primitiveSmall : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤coupledPrimitiveRadius parameters parameters.length compact)
    (insideSeed : originalCoefficientSeed parameters compact state.val.val∈Seed.parameterDomain)
    (physicalState : QuotientState parameters)
    (sameBase : physicalState.2.1=planarReferenceCore parameters+state.val.val.field)
    (sameEpsilon : physicalState.1=(state.val.val.epsilon:ℂ))
    (vector : ACore parameters 3) (scalar : ACore parameters 1)
    (constrained : VectorConstraints parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed (toPhysicalCore parameters vector))
    (homogeneous : quotientRowsDerivative parameters parameters.length 1 physicalState ![(0,vector,scalar)]=0)

include lengthPositive small widthHalf widthLength primitiveSmall insideSeed sameBase sameEpsilon constrained homogeneous

/-- Original U vanishes at every actual closed collar point, by the same
covariant inverse frame used in its accepted reconstruction. -/
theorem originalPhysicalU_circle_zero
    (lower : ℝ) (positive : 0<lower) (domain : lower≤min (1/2) parameters.length)
    (radius : Icc lower (1:ℝ)) (angles : ℝ×ℝ) :
    originalCoreCircle parameters vector ⟨radius.val,positive.le.trans radius.property.1,radius.property.2⟩ angles=0 := by
  let bounded : lower<1 := (domain.trans (min_le_left _ _)).trans_lt (by norm_num)
  let curves := originalPolarCovariantCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
    lower positive bounded vector
  have traceZero := originalPhysicalCovariant_trace_zero parameters compact lengthPositive widthHalf widthLength state small primitiveSmall insideSeed
    physicalState sameBase sameEpsilon vector scalar constrained homogeneous lower positive domain radius
  have valueZero := originalCurve_traceZero_fullField curves bounded radius traceZero angles
  have recovery := originalPolarCovariantCurves_recovers_U parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
    lower positive bounded vector radius.val radius.property angles
  apply recovery.symm.trans
  rw [SmoothLowPhysicalRow.fullField_physicalUFromPolar parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
    lower positive bounded curves radius.val radius.property angles,valueZero]
  simp [cartesianCovariantValue]

end Grad.OriginalPhysicalKernelUniqueness
