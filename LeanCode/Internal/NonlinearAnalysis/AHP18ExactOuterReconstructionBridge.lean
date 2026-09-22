import AHP17ExactOuterMassBridge

noncomputable section
set_option maxHeartbeats 1800000

namespace Grad.AnnularReconstruction
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualBoundaryInverse

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact)
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialMassLowRadius parameters L compact)

theorem radialMassInverseKernel_one :
    SameKernelEntries (radialMassInverseKernel parameters L compact state outerRadialPoint small)
      (actualMassInverseKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.small state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) := by
  exact (radialMassPerturbationKernel_one parameters L compact state _).negativeIdentityInverse
    _ _ _ _ _ _

theorem radialMassRightHandKernel_one :
    SameKernelEntries (radialMassRightHandKernel parameters L compact state outerRadialPoint small)
      (actualMassRightHandKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.small state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) :=
  (sameConstantMatrixKernel _ _ _ _ _).sub
    (radialKnownJStarKernel_one parameters L compact state _)

theorem radialRecoveredMassKernel_one :
    SameKernelEntries (radialRecoveredMassKernel parameters L compact state outerRadialPoint small)
      (actualRecoveredMassKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.small state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) :=
  (radialMassInverseKernel_one parameters L compact state small).comp
    (radialMassRightHandKernel_one parameters L compact state small)

theorem radialNormalizedCovariantKernel_one :
    SameKernelEntries (radialNormalizedCovariantKernel parameters L compact state outerRadialPoint small)
      (actualCovariantKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.small state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) :=
  ((radialUnknownUKernel_one parameters L compact state _).comp
    (radialRecoveredMassKernel_one parameters L compact state small)).add
    (radialKnownAStarKernel_one parameters L compact state _)

theorem radialNormalizedRotatedCovariantKernel_one :
    SameKernelEntries (radialNormalizedRotatedCovariantKernel parameters L compact state outerRadialPoint small)
      (actualRotatedCovariantKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.small state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) :=
  ((radialUnknownVKernel_one parameters L compact state _).comp
    (radialRecoveredMassKernel_one parameters L compact state small)).add
    (radialKnownRAStarKernel_one parameters L compact state _)

theorem radialSevenSlotKernel_one :
    SameKernelEntries (radialSevenSlotKernel parameters outerRadialPoint)
      (fullIdentityKernel parameters 7) := by
  unfold radialSevenSlotKernel
  rw [radialSevenSlotNormalization_one, constantMatrixKernel_id]
  exact sameFullIdentityKernel _ _ _

/-- Exact recovery of the frozen physical outer-circle covariant kernel. -/
theorem radialCovariantKernel_one :
    SameKernelEntries (radialCovariantKernel parameters L compact state outerRadialPoint small (by norm_num))
      (actualCovariantKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.small state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) := by
  have same := (radialNormalizedCovariantKernel_one parameters L compact state small).comp
    (radialSevenSlotKernel_one parameters)
  rw [fullKernel_comp_identity_rect] at same
  exact same

/-- Exact recovery of the frozen genuine angular-row kernel at r=1. -/
theorem radialRotatedCovariantKernel_one :
    SameKernelEntries (radialRotatedCovariantKernel parameters L compact state outerRadialPoint small (by norm_num))
      (actualRotatedCovariantKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.small state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) := by
  have same := (radialNormalizedRotatedCovariantKernel_one parameters L compact state small).comp
    (radialSevenSlotKernel_one parameters)
  rw [fullKernel_comp_identity_rect] at same
  exact same

end Grad.AnnularReconstruction
