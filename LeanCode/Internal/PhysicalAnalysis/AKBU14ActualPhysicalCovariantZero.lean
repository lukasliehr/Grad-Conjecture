import AKBU13ZeroRetainedTupleTrace

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

/-- Every original slot of the actual homogeneous physical tuple vanishes
on each fixed collar, by the same retained uniqueness theorem. -/
theorem originalPhysicalTuple_coefficients_zero
    (lower : ℝ) (positive : 0<lower) (domain : lower≤min (1/2) parameters.length)
    (radius : Icc lower (1:ℝ)) (slot : Fin 4) (mode : ℤ×ℤ) :
    originalPhysicalCoefficient
      ((originalKernelSmoothTuple parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
        lower positive ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) physicalState.2.1 vector scalar).val slot) radius.val mode=0 := by
  have zero := originalPhysicalRetained_eq_zero parameters compact lengthPositive widthHalf widthLength state small primitiveSmall insideSeed
    physicalState sameBase sameEpsilon vector scalar constrained homogeneous lower positive domain
  have represented := originalPhysicalKernelGraphPoint_represents parameters parameters.length compact lower positive domain lengthPositive state small
    physicalState.2.1 vector scalar
  have pair := originalObservedTuple_retainedZero parameters parameters.length compact lower positive
    ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) lengthPositive state _ _ represented zero radius mode
  fin_cases slot
  · exact pair.1
  · exact pair.2
  · change originalPhysicalCoefficient (0 : OriginalPhysicalField) radius.val mode=0
    simp [originalPhysicalCoefficient,Grad.BoundaryTrace.angularCoefficient_zero]
  · change originalPhysicalCoefficient (0 : OriginalPhysicalField) radius.val mode=0
    simp [originalPhysicalCoefficient,Grad.BoundaryTrace.angularCoefficient_zero]

/-- Exact SAME inverse recovery now forces the original physical covariant
trace to zero; no replacement field or graph membership hypothesis occurs. -/
theorem originalPhysicalCovariant_trace_zero
    (lower : ℝ) (positive : 0<lower) (domain : lower≤min (1/2) parameters.length)
    (radius : Icc lower (1:ℝ)) :
    originalCurveNegativeTrace
      (originalPolarCovariantCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
        lower positive ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) vector) radius=0 := by
  have recovered := originalHomogeneous_covariantRecovery parameters compact lengthPositive.ne' state small insideSeed lower positive
    ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) physicalState sameBase sameEpsilon vector scalar constrained homogeneous radius
  have seven := originalTuple_sevenZero parameters lower positive
    (originalKernelSmoothTuple parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
      lower positive ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) physicalState.2.1 vector scalar) radius
    (originalPhysicalTuple_coefficients_zero parameters compact lengthPositive widthHalf widthLength state small primitiveSmall insideSeed
      physicalState sameBase sameEpsilon vector scalar constrained homogeneous lower positive domain radius)
  apply recovered.trans
  unfold tupleCovariantTrace
  rw [seven,map_zero,map_zero]

end Grad.OriginalPhysicalKernelUniqueness
