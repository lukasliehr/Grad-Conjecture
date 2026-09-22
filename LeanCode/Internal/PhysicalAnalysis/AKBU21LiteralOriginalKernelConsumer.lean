import AKBU20ActualOriginalPhysicalPairUniqueness

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
    (homogeneous : quotientRowsDerivative parameters parameters.length 1 physicalState ![(0,vector,scalar)]=0)

include lengthPositive small widthHalf widthLength primitiveSmall insideSeed sameBase sameEpsilon homogeneous

namespace Consumer

/-- Literal original real smooth-domain physical kernel uniqueness. The
stored vector is the existing toPhysicalCore involution of U. Both gauge
constraints, all flat jets, the original outer row and scalar mean are
obtained from the actual domain projection; none is inserted as a replacement premise. -/
theorem originalSmoothDomain_physicalKernel_zero
    (member : (0,toPhysicalCore parameters vector,scalar)∈
      Grad.RealFixedRanges.stateSmoothRange parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed) :
    vector=0 ∧ scalar=0 := by
  have fixed := (Grad.RealFixedRanges.mem_stateSmoothRange parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed _).mp member
  have constraints := fullProjection_constraints parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed
    (0,toPhysicalCore parameters vector,scalar)
  rw [fixed.1] at constraints
  exact originalPhysical_pair_eq_zero parameters compact lengthPositive widthHalf widthLength state small primitiveSmall insideSeed
    physicalState sameBase sameEpsilon vector scalar constraints.1 homogeneous constraints.2

end Consumer
end Grad.OriginalPhysicalKernelUniqueness
