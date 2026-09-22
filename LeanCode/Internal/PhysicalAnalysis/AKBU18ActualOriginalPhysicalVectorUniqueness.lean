import AKBU17OriginalCircleFaithfulness

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
    (constrained : VectorConstraints parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed (toPhysicalCore parameters vector))
    (homogeneous : quotientRowsDerivative parameters parameters.length 1 physicalState ![(0,vector,scalar)]=0)

include lengthPositive small widthHalf widthLength primitiveSmall insideSeed sameBase sameEpsilon constrained homogeneous

/-- The original constrained homogeneous physical vector is zero as an
actual all-grade Cartesian core, including the axis. -/
theorem originalPhysicalU_eq_zero : vector=0 := by
  have flat : ∀ cell,ZeroCartesianFirstJets (vector.val cell) := by
    simpa only [toPhysicalCore_involutive] using toPhysicalCore_zeroJets parameters (toPhysicalCore parameters vector) constrained.1
  apply originalCore_zero_of_positiveCircles parameters vector
    (fun cell => ((zeroCartesianFirstJets_iff _).mp (flat cell)).1)
  intro radius radiusPositive angles
  let lower := min radius.val (min (1/2) parameters.length)/2
  have positive : 0<lower := div_pos (lt_min radiusPositive (lt_min (by norm_num) lengthPositive)) (by norm_num)
  have bounded : lower≤min radius.val (min (1/2) parameters.length) := by
    dsimp only [lower]
    linarith [le_of_lt (lt_min radiusPositive (lt_min (by norm_num : (0:ℝ)<1/2) lengthPositive))]
  have inside : lower≤radius.val := bounded.trans (min_le_left _ _)
  have domain : lower≤min (1/2) parameters.length := bounded.trans (min_le_right _ _)
  exact originalPhysicalU_circle_zero parameters compact lengthPositive widthHalf widthLength state small primitiveSmall insideSeed
    physicalState sameBase sameEpsilon vector scalar constrained homogeneous lower positive domain ⟨radius.val,inside,radius.property.2⟩ angles

end Grad.OriginalPhysicalKernelUniqueness
