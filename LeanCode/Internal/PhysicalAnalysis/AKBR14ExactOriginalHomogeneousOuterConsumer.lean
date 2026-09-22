import AKBR13ActualOriginalOuterBoundaryZero

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
namespace Grad.OriginalKernelOuterUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.SourceCollarFullSource Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.OriginalKernelGraphRestriction Grad.OriginalKernelRetainedDecay Grad.OriginalKernelCovariantRecovery Grad.Constraints Grad.Cor18
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.NonlinearQuotientBounds Grad.PhysicalCoordinates Grad.SourceCollar Grad.FinitePhysicalJetLift Grad.NonlinearRange
open Grad.AnnularOriginalCoreRealization Grad.AnnularFullGraph Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.AnnularForwardTraces
open Grad.AnnularCurrentSource Grad.AnnularSourceGraph

namespace Consumer

/-- The original smooth constrained homogeneous Cartesian field enters the
SAME original full graph with ALL FOUR source coordinates and the complete
original high-plus-low outer row zero. Original total frame, physical
fields, analytic width and computed retained tuple are unchanged. -/
theorem originalPhysical_homogeneousGraph_allRows
    (parameters : PhaseParameters) (compact : ℝ) (lengthPositive : 0<parameters.length)
    (widthHalf : parameters.gamma≤1/2) (widthLength : parameters.gamma≤Real.sqrt 5/(6*parameters.length))
    (state : RetainedInverseState parameters parameters.length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤
      originalCoefficientLowRadius parameters parameters.length)
    (primitiveSmall : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8≤
      coupledPrimitiveRadius parameters parameters.length compact)
    (insideSeed : originalCoefficientSeed parameters compact state.val.val∈Seed.parameterDomain)
    (lower : ℝ) (positive : 0<lower) (domain : lower≤min (1/2) parameters.length)
    (physicalState : QuotientState parameters)
    (sameBase : physicalState.2.1=planarReferenceCore parameters+state.val.val.field)
    (sameEpsilon : physicalState.1=(state.val.val.epsilon : ℂ))
    (vector : ACore parameters 3) (scalar : ACore parameters 1)
    (constrained : VectorConstraints parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed
      (toPhysicalCore parameters vector))
    (homogeneous : quotientRowsDerivative parameters parameters.length 1 physicalState ![(0,vector,scalar)]=0) :
    let point := originalPhysicalKernelGraphPoint parameters parameters.length compact lower positive domain lengthPositive state small
      physicalState.2.1 vector scalar
    point∈OriginalObservedEquationGraph parameters parameters.length compact lower positive (domain.trans (min_le_left _ _)) lengthPositive
      widthHalf widthLength state ∧ point.ofLp.2=0 ∧
      originalOuterBoundaryTrace parameters parameters.length compact lower positive (domain.trans (min_le_left _ _)) lengthPositive state
        (point.ofLp.1,point.ofLp.2.ofLp.1)=0 := by
  have graph := Grad.OriginalKernelHomogeneousGraph.Consumer.originalPhysical_homogeneousGraph_sources parameters compact lengthPositive
    widthHalf widthLength state small primitiveSmall insideSeed lower positive domain physicalState sameBase sameEpsilon vector scalar constrained homogeneous
  exact ⟨graph.1,graph.2,originalPhysicalKernelGraphPoint_outer parameters compact lengthPositive state small insideSeed lower positive domain
    physicalState sameBase sameEpsilon vector scalar constrained homogeneous⟩

end Consumer
end Grad.OriginalKernelOuterUniqueness
