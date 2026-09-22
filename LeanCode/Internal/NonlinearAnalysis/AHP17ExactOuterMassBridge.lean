import AHP16ExactOuterEncodedBridge

noncomputable section
set_option maxHeartbeats 2000000

namespace Grad.AnnularReconstruction
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact)
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialFirstLowRadius parameters L compact)

theorem radialKnownWKernel_one :
    SameKernelEntries (radialKnownWKernel parameters L compact state outerRadialPoint small)
      (actualKnownEncodedWKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.firstSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) :=
  (radialEncodedFirstInverseKernel_one parameters L compact state small).comp
    (radialKnownEncodedDataKernel_one parameters L compact state small)

theorem radialKnownAStarKernel_one :
    SameKernelEntries (radialKnownAStarKernel parameters L compact state outerRadialPoint small)
      (actualKnownAStarKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.firstSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) :=
  (radialGaugeQKernel_one parameters L compact state _).comp
    (((sameEncodedJKernel _ _).comp (radialKnownWKernel_one parameters L compact state small)).add
      ((sameConstantMatrixKernel _ _ _ _ _).comp (sameConstantMatrixKernel _ _ _ _ _)))

theorem radialKnownRAStarKernel_one :
    SameKernelEntries (radialKnownRAStarKernel parameters L compact state outerRadialPoint small)
      (actualKnownRAStarKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.firstSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) :=
  ((sameEncodedRotationKernel _ _).comp (radialKnownWKernel_one parameters L compact state small)).add
    (radialKnownRotatedQStarKernel_one parameters)

private theorem unknownQA_one :
    SameKernelEntries (radialUnknownGaugeQAKernel parameters L compact state outerRadialPoint small)
      (fullKernelComposition
        (actualGaugeQKernelOnBall parameters L state.rho state.alpha state.delta state.parameter
          state.epsilon compact state.field state.gaugeSmall state.compactNonnegative
          state.alphaSmall state.deltaSmall state.parameterSmall)
        (actualUnknownQAKernel parameters)) :=
  (radialGaugeQKernel_one parameters L compact state _).comp (sameUnknownQAKernel _ _)

theorem radialUnknownN0Kernel_one :
    SameKernelEntries (radialUnknownN0Kernel parameters L compact state outerRadialPoint small)
      (actualUnknownN0Kernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.firstSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) :=
  (sameConstantMatrixKernel _ _ _ _ _).comp
    (((sameScalarModeDiagonalKernel _ _ _ _ _ _).comp
      ((radialForceKernel_one parameters L compact state 0).comp
        (unknownQA_one parameters L compact state small))).neg)

theorem radialUnknownN1Kernel_one :
    SameKernelEntries (radialUnknownN1Kernel parameters L compact state outerRadialPoint small)
      (actualUnknownN1Kernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.firstSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) :=
  (sameConstantMatrixKernel _ _ _ _ _).comp
    (((sameFullIdentityKernel _ _ _).smul 2).sub
      (((radialRotatedForceKernel_one parameters L compact state 0).comp
        (unknownQA_one parameters L compact state small)).add
        ((radialForceKernel_one parameters L compact state 0).comp (sameConstantMatrixKernel _ _ _ _ _))))

theorem radialUnknownN2Kernel_one :
    SameKernelEntries (radialUnknownN2Kernel parameters L compact state outerRadialPoint small)
      (actualUnknownN2Kernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.firstSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) :=
  (sameConstantMatrixKernel _ _ _ _ _).comp
    (((sameScalarModeDiagonalKernel _ _ _ _ _ _).comp
      ((radialForceKernel_one parameters L compact state 1).comp
        (unknownQA_one parameters L compact state small))).neg)

theorem radialUnknownNKernel_one :
    SameKernelEntries (radialUnknownNKernel parameters L compact state outerRadialPoint small)
      (actualUnknownNKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.firstSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) :=
  (radialUnknownN0Kernel_one parameters L compact state small).add
    ((radialUnknownN1Kernel_one parameters L compact state small).add
      (radialUnknownN2Kernel_one parameters L compact state small))

theorem radialUnknownWKernel_one :
    SameKernelEntries (radialUnknownWKernel parameters L compact state outerRadialPoint small)
      (actualUnknownWKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.firstSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) :=
  (radialEncodedFirstInverseKernel_one parameters L compact state small).comp
    (radialUnknownNKernel_one parameters L compact state small)

theorem radialUnknownUKernel_one :
    SameKernelEntries (radialUnknownUKernel parameters L compact state outerRadialPoint small)
      (actualUnknownUKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.firstSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) :=
  (radialGaugeQKernel_one parameters L compact state _).comp
    (((sameEncodedJKernel _ _).comp (radialUnknownWKernel_one parameters L compact state small)).add
      (sameUnknownQAKernel _ _))

theorem radialUnknownVKernel_one :
    SameKernelEntries (radialUnknownVKernel parameters L compact state outerRadialPoint small)
      (actualUnknownVKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.firstSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) :=
  ((sameEncodedRotationKernel _ _).comp (radialUnknownWKernel_one parameters L compact state small)).add
    (sameConstantMatrixKernel _ _ _ _ _)

theorem radialSigmaKernel_one :
    SameKernelEntries (radialSigmaKernel parameters L compact state outerRadialPoint 0)
      (actualSigmaBoundaryKernel parameters L state.rho state.epsilon state.field state.coefficientSmall) :=
  radialSigmaKernel_one_entry parameters L compact state

theorem radialRotatedSigmaKernel_one :
    SameKernelEntries (radialRotatedSigmaKernel parameters L compact state outerRadialPoint 0)
      (actualRotatedSigmaBoundaryKernel parameters L state.rho state.epsilon state.field state.coefficientSmall) := by
  intro shift mode
  rfl

theorem radialSigmaComponentKernel_one (component : Fin 3) :
    SameKernelEntries (radialSigmaComponentKernel parameters L compact state outerRadialPoint component)
      (actualSigmaComponentBoundaryKernel parameters L state.rho state.epsilon state.field state.coefficientSmall component) := by
  intro shift mode
  rfl

theorem radialRotatedSigmaComponentKernel_one (component : Fin 3) :
    SameKernelEntries (radialRotatedSigmaComponentKernel parameters L compact state outerRadialPoint component)
      (actualRotatedSigmaComponentBoundaryKernel parameters L state.rho state.epsilon state.field state.coefficientSmall component) := by
  intro shift mode
  rfl

theorem radialKnownJStarKernel_one :
    SameKernelEntries (radialKnownJStarKernel parameters L compact state outerRadialPoint small)
      (actualKnownJStarKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.firstSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) :=
  (sameScalarModeDiagonalKernel _ _ _ _ _ _).comp
    ((((radialRotatedSigmaKernel_one parameters L compact state).comp
      (radialKnownAStarKernel_one parameters L compact state small)).add
      ((radialSigmaKernel_one parameters L compact state).comp
        (radialKnownRAStarKernel_one parameters L compact state small))).add
      (((radialRotatedSigmaComponentKernel_one parameters L compact state 1).comp
        (sameConstantMatrixKernel _ _ _ _ _)).add
        ((radialSigmaComponentKernel_one parameters L compact state 1).comp
          (sameConstantMatrixKernel _ _ _ _ _))))

theorem radialMassPerturbationKernel_one :
    SameKernelEntries (radialMassPerturbationKernel parameters L compact state outerRadialPoint small)
      (actualMassPerturbationKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.firstSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) :=
  (sameScalarModeDiagonalKernel _ _ _ _ _ _).comp
    (((radialRotatedSigmaKernel_one parameters L compact state).comp
      (radialUnknownUKernel_one parameters L compact state small)).add
      ((radialSigmaKernel_one parameters L compact state).comp
        (radialUnknownVKernel_one parameters L compact state small)))

end Grad.AnnularReconstruction
