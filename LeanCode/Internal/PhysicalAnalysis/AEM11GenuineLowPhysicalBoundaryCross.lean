import AEM10ActualLowSevenBoundaryInput

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

variable (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (state : RetainedInverseState parameters length compact)

def lowStateBoundaryPR : SevenSlotTrace parameters 0 0 →L[ℂ] HighBoundaryPrimitive parameters 0 0 :=
  actualPhysicalBoundaryPR parameters length state.boundaryState.val.rho state.boundaryState.val.alpha
    state.boundaryState.val.delta state.boundaryState.val.parameter state.boundaryState.val.epsilon compact
    state.boundaryState.val.field state.boundaryState.property state.boundaryState.val.compactNonnegative
    state.boundaryState.val.alphaSmall state.boundaryState.val.deltaSmall state.boundaryState.val.parameterSmall 0 0

/-- BF16 has the negative of the actual high physical primitive beta.
The inherited coordinate is its genuine angular derivative, -R beta. -/
def lowToHighBoundaryCross : lowEnergyGraph lower length positive →L[ℂ] HighBoundaryPrimitive parameters 0 0 :=
  -(lowStateBoundaryPR parameters length compact state ∘L
    lowOuterSevenTrace parameters lower length lengthPositive positive lowerHalf)

theorem lowOuterX_highProjection_zero (field : lowEnergyGraph lower length positive) :
    fullNegativeKernelAction parameters 0 0 (highAngularKernel parameters 1)
      (lowOuterXNegative parameters lower length lengthPositive positive lowerHalf field) = 0 := by
  apply NegativeTrace.ext_coefficient parameters 0 0
  intro mode
  rw [highAngularKernel_coefficient]
  have zeroCoefficient : negativeTraceCoefficient parameters 0 0 (0 : NegativeTrace parameters 0 0 1) mode = 0 := by simp [negativeTraceCoefficient]
  rw [zeroCoefficient]
  by_cases high : 3 ≤ |mode.1|
  · have outside : ¬ (|mode.1| = 1 ∨ |mode.1| = 2) := by omega
    unfold negativeTraceCoefficient
    rw [lowOuterXNegative_outside parameters lower length lengthPositive positive lowerHalf field mode outside, smul_zero, smul_zero]
  · simp only [highAngularMultiplier, high, ↓reduceIte, zero_smul]

theorem lowBoundary_reference_zero (field : lowEnergyGraph lower length positive) :
    fullSevenSlotKernelAction parameters 0 0
      (fullKernelComposition (highAngularKernel parameters 1) (sevenInputSlotKernel parameters 0))
      (lowOuterSevenTrace parameters lower length lengthPositive positive lowerHalf field) = 0 := by
  unfold fullSevenSlotKernelAction
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    sevenInputSlotKernel_action]
  exact lowOuterX_highProjection_zero parameters lower length lengthPositive positive lowerHalf field

theorem lowBoundary_actual_deviation (field : lowEnergyGraph lower length positive) :
    (lowStateBoundaryPR parameters length compact state
      (lowOuterSevenTrace parameters lower length lengthPositive positive lowerHalf field)).val =
      fullSevenSlotKernelAction parameters 0 0 state.boundaryState.fullBoundaryDeviation
        (lowOuterSevenTrace parameters lower length lengthPositive positive lowerHalf field) := by
  change fullSevenSlotKernelAction parameters 0 0 state.boundaryState.physicalRow _ = _
  rw [← full_physical_boundary_reference_difference state.boundaryState]
  unfold fullSevenSlotKernelAction
  simp only [ContinuousLinearMap.comp_apply]
  rw [fullNegativeKernelAction_add]
  have zero := lowBoundary_reference_zero parameters lower length lengthPositive positive lowerHalf field
  change fullNegativeKernelAction parameters 0 0
    (fullKernelComposition (highAngularKernel parameters 1) (sevenInputSlotKernel parameters 0))
    (sevenSlotFlatten parameters 0 0 (lowOuterSevenTrace parameters lower length lengthPositive positive lowerHalf field)) = 0 at zero
  rw [zero, add_zero]

theorem lowToHighBoundaryCross_derivativeCoordinate (field : lowEnergyGraph lower length positive) :
    (lowToHighBoundaryCross parameters lower length compact lengthPositive positive lowerHalf state field).val =
      -fullSevenSlotKernelAction parameters 0 0 state.boundaryState.fullBoundaryDeviation
        (lowOuterSevenTrace parameters lower length lengthPositive positive lowerHalf field) := by
  change -(lowStateBoundaryPR parameters length compact state
    (lowOuterSevenTrace parameters lower length lengthPositive positive lowerHalf field)).val = _
  rw [lowBoundary_actual_deviation]

theorem lowStateBoundaryPR_genuine (field : lowEnergyGraph lower length positive) :
    highBoundaryPrimitiveTrace parameters 0 0
      (lowStateBoundaryPR parameters length compact state
        (lowOuterSevenTrace parameters lower length lengthPositive positive lowerHalf field)) =
      actualHighPhysicalBoundary parameters length state.boundaryState.val.rho state.boundaryState.val.alpha
        state.boundaryState.val.delta state.boundaryState.val.parameter state.boundaryState.val.epsilon compact
        state.boundaryState.val.field state.boundaryState.property state.boundaryState.val.compactNonnegative
        state.boundaryState.val.alphaSmall state.boundaryState.val.deltaSmall state.boundaryState.val.parameterSmall 0 0
        (lowOuterSevenTrace parameters lower length lengthPositive positive lowerHalf field) :=
  actualPhysicalBoundaryPR_eq_high parameters length state.boundaryState.val.rho state.boundaryState.val.alpha
    state.boundaryState.val.delta state.boundaryState.val.parameter state.boundaryState.val.epsilon compact
    state.boundaryState.val.field state.boundaryState.property state.boundaryState.val.compactNonnegative
    state.boundaryState.val.alphaSmall state.boundaryState.val.deltaSmall state.boundaryState.val.parameterSmall 0 0 _
    (lowOuterSevenTrace_meanFree parameters lower length lengthPositive positive lowerHalf field)
    (lowOuterSevenTrace_derivative parameters lower length lengthPositive positive lowerHalf field)

end Grad.AnnularCrossMaps
