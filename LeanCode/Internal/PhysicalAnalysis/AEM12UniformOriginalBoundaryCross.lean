import AEM11GenuineLowPhysicalBoundaryCross

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCrossMaps
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.BoundaryKernelAction Grad.PhaseAlgebra Grad.BoundaryTrace
open Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse Grad.AnnularReconstruction
open Grad.GaugeCoefficients.Physical.Allocation

def lowBoundaryErrorConstant (parameters : PhaseParameters) (length compact : ℝ) : ℝ :=
  Classical.choose (fullBoundaryDeviation_vanishingMoments parameters length compact 1)

theorem lowBoundaryErrorConstant_nonnegative (parameters : PhaseParameters) (length compact : ℝ) :
    0 ≤ lowBoundaryErrorConstant parameters length compact :=
  (Classical.choose_spec (fullBoundaryDeviation_vanishingMoments parameters length compact 1)).1

theorem lowBoundaryError_moment (parameters : PhaseParameters) (length compact : ℝ)
    (state : RetainedInverseState parameters length compact) :
    fullKernelMoment parameters 1 state.boundaryState.fullBoundaryDeviation ≤
      lowBoundaryErrorConstant parameters length compact *
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 :=
  (Classical.choose_spec (fullBoundaryDeviation_vanishingMoments parameters length compact 1)).2 state.boundaryState

theorem lowToHighBoundaryCross_B8 (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (state : RetainedInverseState parameters length compact) (field : lowEnergyGraph lower length positive) :
    ‖lowToHighBoundaryCross parameters lower length compact lengthPositive positive lowerHalf state field‖ ≤
      (lowBoundaryErrorConstant parameters length compact * lowOuterSevenConstant length) *
        physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 * ‖field‖ := by
  change ‖(lowToHighBoundaryCross parameters lower length compact lengthPositive positive lowerHalf state field).val‖ ≤ _
  rw [lowToHighBoundaryCross_derivativeCoordinate, norm_neg]
  apply (fullSevenSlotKernelAction_bound parameters 0 0 state.boundaryState.fullBoundaryDeviation _).trans
  have moment := lowBoundaryError_moment parameters length compact state
  have inputBound := lowOuterSevenLinear_bound parameters lower length lengthPositive positive lowerHalf field
  have budgetNonnegative := physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8
  have constantNonnegative := lowBoundaryErrorConstant_nonnegative parameters length compact
  have first := mul_le_mul_of_nonneg_right moment
    (norm_nonneg (lowOuterSevenTrace parameters lower length lengthPositive positive lowerHalf field))
  have second := mul_le_mul_of_nonneg_left inputBound (mul_nonneg constantNonnegative budgetNonnegative)
  exact (first.trans second).trans_eq (by ring)

/-- The sign in BF16 applies to the genuine physical primitive, not merely
its angular derivative coordinates. -/
theorem lowToHighBoundaryCross_genuine (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (state : RetainedInverseState parameters length compact) (field : lowEnergyGraph lower length positive) :
    highBoundaryPrimitiveTrace parameters 0 0
      (lowToHighBoundaryCross parameters lower length compact lengthPositive positive lowerHalf state field) =
      -actualHighPhysicalBoundary parameters length state.boundaryState.val.rho state.boundaryState.val.alpha
        state.boundaryState.val.delta state.boundaryState.val.parameter state.boundaryState.val.epsilon compact
        state.boundaryState.val.field state.boundaryState.property state.boundaryState.val.compactNonnegative
        state.boundaryState.val.alphaSmall state.boundaryState.val.deltaSmall state.boundaryState.val.parameterSmall 0 0
        (lowOuterSevenTrace parameters lower length lengthPositive positive lowerHalf field) := by
  change fullNegativeKernelAction parameters 0 0 (angularInverseKernel parameters 1)
    (-(lowStateBoundaryPR parameters length compact state
      (lowOuterSevenTrace parameters lower length lengthPositive positive lowerHalf field)).val) = _
  rw [map_neg]
  exact congrArg Neg.neg (lowStateBoundaryPR_genuine parameters lower length compact lengthPositive positive lowerHalf state field)

end Grad.AnnularCrossMaps
