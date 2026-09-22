import AKBR12OriginalBoundaryPrimitiveZero

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
open Set
namespace Grad.OriginalKernelOuterUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Cor18 Grad.PhysicalCoordinates
open Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceBoundaryTrace Grad.SourceCollarFullSource
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.AnnularCrossMaps
open Grad.AnnularOriginalSmoothCore Grad.OriginalKernelCovariantRecovery Grad.ActualSmoothPhysicalField
open Grad.OriginalKernelGraphRestriction Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.NonlinearQuotientBounds Grad.SourceCollar Grad.NonlinearRange
open Grad.AnnularForwardTraces
open Grad.FinitePhysicalJetLift Grad.AnnularCurrentSource
open Grad.AnnularFullGraph Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse

variable (parameters : PhaseParameters) (compact : ℝ) (lengthPositive : 0<parameters.length)
    (state : RetainedInverseState parameters parameters.length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤
      originalCoefficientLowRadius parameters parameters.length)
    (insideSeed : originalCoefficientSeed parameters compact state.val.val∈Seed.parameterDomain)
    (lower : ℝ) (positive : 0<lower) (domain : lower≤min (1/2) parameters.length)
    (physicalState : QuotientState parameters)
    (sameBase : physicalState.2.1=planarReferenceCore parameters+state.val.val.field)
    (sameEpsilon : physicalState.1=(state.val.val.epsilon : ℂ))
    (vector : ACore parameters 3) (scalar : ACore parameters 1)
    (constrained : VectorConstraints parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed
      (toPhysicalCore parameters vector))
    (homogeneous : quotientRowsDerivative parameters parameters.length 1 physicalState ![(0,vector,scalar)]=0)

include insideSeed sameBase sameEpsilon constrained homogeneous

/-- The SAME original physical homogeneous graph point has its genuine
full high-plus-low outer boundary row zero. This is the exact original
CP7 constraint transported through BCT, with no additional boundary premise. -/
theorem originalPhysicalKernelGraphPoint_outer :
    let point := originalPhysicalKernelGraphPoint parameters parameters.length compact lower positive domain lengthPositive state small
      physicalState.2.1 vector scalar
    originalOuterBoundaryTrace parameters parameters.length compact lower positive (domain.trans (min_le_left _ _)) lengthPositive state
      (point.ofLp.1,point.ofLp.2.ofLp.1)=0 := by
  dsimp only
  let bounded : lower<1 := (domain.trans (min_le_left _ _)).trans_lt (by norm_num)
  let tuple := originalKernelSmoothTuple parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field small
    lower positive bounded physicalState.2.1 vector scalar
  let point := originalPhysicalKernelGraphPoint parameters parameters.length compact lower positive domain lengthPositive state small
    physicalState.2.1 vector scalar
  have represented := originalPhysicalKernelGraphPoint_represents parameters parameters.length compact lower positive domain lengthPositive state small
    physicalState.2.1 vector scalar
  have copied := originalPhysicalKernelGraphPoint_copiedSources parameters parameters.length compact lower positive domain lengthPositive state small
    physicalState.2.1 vector scalar
  rw [copied,originalOuterBoundary_fullSeven]
  have same := originalObserved_fullOuterSeven parameters parameters.length compact lower positive (domain.trans (min_le_left _ _))
    lengthPositive state tuple point represented rfl rfl
  apply (congrArg (lowStateBoundaryPR parameters parameters.length compact state) same).trans
  apply originalTupleBoundaryPrimitive_zero parameters compact state lower positive bounded vector insideSeed constrained tuple
  exact (originalHomogeneous_covariantRecovery parameters compact lengthPositive.ne' state small insideSeed lower positive bounded physicalState
    sameBase sameEpsilon vector scalar constrained homogeneous ⟨1,bounded.le,le_rfl⟩).symm

end Grad.OriginalKernelOuterUniqueness
