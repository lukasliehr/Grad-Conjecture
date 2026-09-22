import AKBI12ActualHomogeneousFirstResidual

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.SourceCollarFullSource Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.OriginalKernelGraphRestriction Grad.OriginalKernelRetainedDecay Grad.OriginalKernelCovariantRecovery Grad.Constraints Grad.Cor18
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.NonlinearQuotientBounds Grad.PhysicalCoordinates Grad.SourceCollar Grad.FinitePhysicalJetLift Grad.NonlinearRange
open Grad.AnnularOriginalCoreRealization Grad.AnnularFullGraph Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.AnnularCurrentSource Grad.AnnularSourceGraph

theorem originalTupleObservation_firstSource_zero {parameters : PhaseParameters} {length compact lower : ℝ}
    {positive : 0<lower} {bounded : lower<1} {lengthPositive : 0<length}
    {state : RetainedInverseState parameters length compact} {tuple : OriginalSmoothTuple parameters lower}
    {point : OriginalFiveBlockAmbient parameters lower length positive}
    (represented : OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state tuple point)
    (zeroResidual : ∀ radius mode,originalTupleF1 parameters length compact lower positive state tuple radius mode=0) :
    point.ofLp.2.ofLp.2.ofLp.1=0 := by
  have zeroRep : OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state 0 0 := by
    simpa only [map_zero] using
      originalTupleGraphLinear_represents parameters length compact lower positive bounded lengthPositive state 0
  apply originalF1Coefficient_faithful parameters lower positive bounded.le
  filter_upwards [represented.firstResidual,zeroRep.firstResidual,ae_restrict_mem measurableSet_Icc] with radius actual zero inside
  intro mode
  have zeroComputed : originalTupleF1 parameters length compact lower positive state 0 ⟨radius,inside⟩ mode=0 := by
    rw [← originalTupleF1Linear_apply,map_zero]
  exact ((actual inside mode).symm.trans (zeroResidual ⟨radius,inside⟩ mode)).trans
    (zeroComputed.symm.trans (zero inside mode))

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

include sameBase sameEpsilon constrained homogeneous

/-- The computed F1 coordinate of the actual original physical graph is
zero, in its original source norm and on the full original collar domain. -/
theorem originalPhysicalKernelGraphPoint_firstSource :
    (originalPhysicalKernelGraphPoint parameters parameters.length compact lower positive domain lengthPositive state small
      physicalState.2.1 vector scalar).ofLp.2.ofLp.2.ofLp.1=0 := by
  apply originalTupleObservation_firstSource_zero
    (originalPhysicalKernelGraphPoint_represents parameters parameters.length compact lower positive domain lengthPositive state small
      physicalState.2.1 vector scalar)
  intro radius mode
  exact originalHomogeneous_tupleF1_zero parameters compact lengthPositive.ne' state small insideSeed lower positive
    ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) physicalState sameBase sameEpsilon vector scalar constrained homogeneous radius mode

end Grad.OriginalKernelHomogeneousGraph
