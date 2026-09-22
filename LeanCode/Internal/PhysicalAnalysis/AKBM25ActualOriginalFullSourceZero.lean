import AKBM24ActualOriginalThirdResidualZero

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

/-- Vanishing of the computed G3 on the open collar kills the complete
original strengthened G3 source carrier; both endpoint representatives are
irrelevant only at this L2 source step. -/
theorem originalTupleObservation_thirdSource_zero {parameters : PhaseParameters} {length compact lower : ℝ}
    {positive : 0<lower} {bounded : lower<1} {lengthPositive : 0<length}
    {state : RetainedInverseState parameters length compact} {tuple : OriginalSmoothTuple parameters lower}
    {point : OriginalFiveBlockAmbient parameters lower length positive}
    (represented : OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state tuple point)
    (zeroResidual : ∀ radius : Icc lower (1:ℝ),radius.val∈Ioo lower 1→∀ mode,
      originalTupleG3 parameters length compact lower positive state tuple radius mode=0) :
    point.ofLp.2.ofLp.2.ofLp.2=0 := by
  have zeroRep : OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state 0 0 := by
    simpa only [map_zero] using originalTupleGraphLinear_represents parameters length compact lower positive bounded lengthPositive state 0
  have interior : ∀ᵐ radius : ℝ ∂volume.restrict (Icc lower 1),radius∈Ioo lower 1 := by
    have equality : (volume : Measure ℝ).restrict (Icc lower 1)=volume.restrict (Ioo lower 1) :=
      Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
    rw [equality]
    exact ae_restrict_mem measurableSet_Ioo
  apply originalF1Coefficient_faithful parameters lower positive bounded.le
  filter_upwards [represented.strengthenedThird,zeroRep.strengthenedThird,interior] with radius actual zero inside
  intro mode
  have closed : radius∈Icc lower 1 := ⟨inside.1.le,inside.2.le⟩
  have zeroComputed : originalTupleG3 parameters length compact lower positive state 0 ⟨radius,closed⟩ mode=0 := by
    rw [← originalTupleG3Linear_apply,map_zero]
  have first := actual closed mode
  have second := zero closed mode
  rw [zeroResidual ⟨radius,closed⟩ inside mode,smul_zero] at first
  rw [zeroComputed,smul_zero] at second
  exact first.symm.trans second

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

/-- The computed original third source is zero for the same actual
homogeneous Cartesian field on the full original fixed-collar domain. -/
theorem originalPhysicalKernelGraphPoint_thirdSource :
    (originalPhysicalKernelGraphPoint parameters parameters.length compact lower positive domain lengthPositive state small
      physicalState.2.1 vector scalar).ofLp.2.ofLp.2.ofLp.2=0 := by
  apply originalTupleObservation_thirdSource_zero
    (originalPhysicalKernelGraphPoint_represents parameters parameters.length compact lower positive domain lengthPositive state small
      physicalState.2.1 vector scalar)
  intro radius interior mode
  exact originalHomogeneous_tupleG3_zero parameters compact lengthPositive.ne' state small insideSeed lower positive
    ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) physicalState sameBase sameEpsilon vector scalar constrained homogeneous radius interior mode

/-- All FOUR actual original source coordinates vanish for this SAME
constructed physical graph point, including the strengthened G3 norm. -/
theorem originalPhysicalKernelGraphPoint_allSources :
    (originalPhysicalKernelGraphPoint parameters parameters.length compact lower positive domain lengthPositive state small
      physicalState.2.1 vector scalar).ofLp.2=0 := by
  have copied := originalPhysicalKernelGraphPoint_copiedSources parameters parameters.length compact lower positive domain lengthPositive state small
    physicalState.2.1 vector scalar
  have first := originalPhysicalKernelGraphPoint_firstSource parameters compact lengthPositive state small insideSeed lower positive domain physicalState
    sameBase sameEpsilon vector scalar constrained homogeneous
  have third := originalPhysicalKernelGraphPoint_thirdSource parameters compact lengthPositive state small insideSeed lower positive domain physicalState
    sameBase sameEpsilon vector scalar constrained homogeneous
  apply (WithLp.equiv 2 _).injective
  exact Prod.ext copied ((WithLp.equiv 2 _).injective (Prod.ext first third))

end Grad.OriginalKernelHomogeneousGraph
