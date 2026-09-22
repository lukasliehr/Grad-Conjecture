import AKBU10SamePhysicalIncomingDecay

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

include widthHalf widthLength primitiveSmall insideSeed sameBase sameEpsilon constrained homogeneous

/-- Original homogeneous graph coercivity now applies to the actual same
physical field. Its incoming payment tends to zero at the original width. -/
theorem originalPhysicalRetained_bound (lower : ℝ) (positive : 0<lower) (domain : lower≤min (1/2) parameters.length) :
    ‖originalWeightedRetainedObservation parameters lower parameters.length positive
      ((domain.trans (min_le_left _ _)).trans (by norm_num)) lengthPositive
      (originalPhysicalKernelGraphPoint parameters parameters.length compact lower positive domain lengthPositive state small physicalState.2.1 vector scalar)‖≤
    (2*Grad.AnnularFullSource.independentCoupledDataConstant parameters parameters.length compact)*
      (originalIncomingDecayConstant parameters parameters.length*lower^(1/4:ℝ)*‖GradeCore.ofCoreLinear (grade:=4) vector‖) := by
  have flat : ∀ cell,ZeroCartesianFirstJets (vector.val cell) := by
    simpa only [toPhysicalCore_involutive] using toPhysicalCore_zeroJets parameters (toPhysicalCore parameters vector) constrained.1
  let context := fixedExhaustionContext parameters parameters.length compact lengthPositive widthHalf widthLength state primitiveSmall lower positive
    (domain.trans (min_le_left _ _))
  let point := originalPhysicalKernelGraphPoint parameters parameters.length compact lower positive domain lengthPositive state small physicalState.2.1 vector scalar
  have equation : point∈Grad.AnnularFullGraph.OriginalObservedEquationGraph parameters parameters.length compact lower positive
      (domain.trans (min_le_left _ _)) lengthPositive widthHalf widthLength state :=
    originalPhysicalKernelGraphPoint_member parameters parameters.length compact lower positive domain lengthPositive widthHalf widthLength state primitiveSmall small physicalState.2.1 vector scalar
  have sources : point.ofLp.2=0 :=
    (Grad.OriginalKernelOuterUniqueness.Consumer.originalPhysical_homogeneousGraph_allRows parameters compact lengthPositive
      widthHalf widthLength state small primitiveSmall insideSeed lower positive domain physicalState sameBase sameEpsilon vector scalar constrained homogeneous).2.1
  have outer : Grad.AnnularForwardTraces.originalOuterBoundaryTrace parameters parameters.length compact lower positive
      (domain.trans (min_le_left _ _)) lengthPositive state (point.ofLp.1,point.ofLp.2.ofLp.1)=0 :=
    (Grad.OriginalKernelOuterUniqueness.Consumer.originalPhysical_homogeneousGraph_allRows parameters compact lengthPositive
      widthHalf widthLength state small primitiveSmall insideSeed lower positive domain physicalState sameBase sameEpsilon vector scalar constrained homogeneous).2.2
  have bound := originalHomogeneousGraph_bound parameters parameters.length compact context point equation sources outer
  have incoming := originalPhysicalIncoming_decay parameters parameters.length compact lower positive domain lengthPositive state small physicalState sameBase
    (GradeCore.ofCoreLinear (grade:=4) vector) flat scalar homogeneous
  change originalWeightedRetainedNorm parameters lower parameters.length positive
    ((domain.trans (min_le_left _ _)).trans (by norm_num)) lengthPositive point.ofLp.1≤_
  exact bound.trans (mul_le_mul_of_nonneg_left incoming
    (mul_nonneg (by norm_num) (Grad.AnnularFullSource.independentCoupledDataConstant_nonnegative parameters parameters.length compact)))

/-- Exact original restriction gives a bound on any fixed collar from
arbitrarily smaller physical collars, all from the same original U,S. -/
theorem originalPhysicalFixedRetained_bound
    (upper : ℝ) (positiveUpper : 0<upper) (domainUpper : upper≤min (1/2) parameters.length)
    (lower : ℝ) (positiveLower : 0<lower) (included : lower≤upper) :
    ‖originalWeightedRetainedObservation parameters upper parameters.length positiveUpper
      ((domainUpper.trans (min_le_left _ _)).trans (by norm_num)) lengthPositive
      (originalPhysicalKernelGraphPoint parameters parameters.length compact upper positiveUpper domainUpper lengthPositive state small physicalState.2.1 vector scalar)‖≤
    (2*Grad.AnnularFullSource.independentCoupledDataConstant parameters parameters.length compact)*
      (originalIncomingDecayConstant parameters parameters.length*lower^(1/4:ℝ)*‖GradeCore.ofCoreLinear (grade:=4) vector‖) := by
  have restriction := originalPhysicalWeightedGraph_restrict parameters parameters.length compact lower upper positiveLower positiveUpper
    (included.trans domainUpper) domainUpper lengthPositive included state small physicalState.2.1 vector scalar
  have normBound := coupledEndpointRestriction_bound lower upper parameters.length positiveLower positiveUpper
    ((domainUpper.trans (min_le_left _ _)).trans_lt (by norm_num)) lengthPositive included
    (originalWeightedRetainedObservation parameters lower parameters.length positiveLower
      (((included.trans domainUpper).trans (min_le_left _ _)).trans (by norm_num)) lengthPositive
      (originalPhysicalKernelGraphPoint parameters parameters.length compact lower positiveLower (included.trans domainUpper) lengthPositive state small physicalState.2.1 vector scalar))
  have sameNorm := congrArg (fun field : CoupledSpace upper parameters.length positiveUpper lengthPositive => ‖field‖) restriction
  exact sameNorm.symm.trans_le (normBound.trans (originalPhysicalRetained_bound parameters compact lengthPositive widthHalf widthLength state small primitiveSmall
    insideSeed physicalState sameBase sameEpsilon vector scalar constrained homogeneous lower positiveLower (included.trans domainUpper)))

end Grad.OriginalPhysicalKernelUniqueness
