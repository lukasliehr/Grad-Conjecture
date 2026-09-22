import AKCS1OriginalConjugateConstraints
import AKBU20ActualOriginalPhysicalPairUniqueness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Set Filter
open scoped Topology ComplexConjugate
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularIncomingIntegrability Grad.AnnularWeightedUniqueness
open Grad.OriginalKernelGraphRestriction Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelOuterUniqueness
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.NonlinearQuotientBounds Grad.FinitePhysicalJetLift Grad.PhysicalCoordinates Grad.Constraints Grad.Cor18
open Grad.AxisSplit
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

    (mean : angularCore parameters 0 scalar=0)
    (source : Grad.QuotientProjection.SmoothQuotient parameters)
    (forward : quotientRowsDerivative parameters parameters.length 1 physicalState ![(0,vector,scalar)]=source)
    (currentReal : Grad.CartesianState.cartesianCoreConjugation parameters physicalState.2.1=physicalState.2.1)
    (sourceReal : Grad.CompletedReality.zCoreConjugation parameters source=source)

open Grad.CompletedReality Grad.OriginalPhysicalKernelUniqueness
include lengthPositive small widthHalf widthLength primitiveSmall insideSeed sameBase sameEpsilon constrained mean forward currentReal sourceReal

/-- Reality of the SAME original physical solution follows from the actual
real operator and complex uniqueness. No reality premise on U or S is used. -/
theorem originalPhysicalPair_real :
    cartesianCoreConjugation parameters vector=vector ∧
    cartesianCoreConjugation parameters scalar=scalar := by
  have scalarReal : conj physicalState.1=physicalState.1 := by
    rw [sameEpsilon]
    exact Complex.conj_ofReal _
  have forwardRaw : physicalEtaZeroRows parameters parameters.length physicalState vector scalar=source := by
    rw [← quotientRowsDerivative_etaZero]
    exact forward
  have conjugateRaw := congrArg (zCoreConjugation parameters) forwardRaw
  rw [physicalEtaZeroRows_conjugate parameters parameters.length physicalState scalarReal currentReal,sourceReal] at conjugateRaw
  have difference := originalConjugateDifference_constraints parameters
    (originalCoefficientSeed parameters compact state.val.val) insideSeed vector scalar constrained mean
  have homogeneous : quotientRowsDerivative parameters parameters.length 1 physicalState
      ![(0,vector-cartesianCoreConjugation parameters vector,scalar-cartesianCoreConjugation parameters scalar)]=0 := by
    rw [quotientRowsDerivative_etaZero]
    change physicalEtaZeroLinear parameters parameters.length physicalState
      ((vector,scalar)-(cartesianCoreConjugation parameters vector,cartesianCoreConjugation parameters scalar))=0
    rw [map_sub]
    change physicalEtaZeroRows parameters parameters.length physicalState vector scalar-
      physicalEtaZeroRows parameters parameters.length physicalState
        (cartesianCoreConjugation parameters vector) (cartesianCoreConjugation parameters scalar)=0
    rw [forwardRaw,conjugateRaw,sub_self]
  have zero := originalPhysical_pair_eq_zero parameters compact lengthPositive widthHalf widthLength state small primitiveSmall insideSeed
    physicalState sameBase sameEpsilon (vector-cartesianCoreConjugation parameters vector)
    (scalar-cartesianCoreConjugation parameters scalar) difference.1 homogeneous difference.2
  exact ⟨(sub_eq_zero.mp zero.1).symm,(sub_eq_zero.mp zero.2).symm⟩

end Grad.OriginalCoreRealization
