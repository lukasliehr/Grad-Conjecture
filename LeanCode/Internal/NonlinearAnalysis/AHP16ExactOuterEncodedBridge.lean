import AHP15ExactOuterGaugeBridge

noncomputable section
set_option maxHeartbeats 1800000

namespace Grad.AnnularReconstruction
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact)
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialFirstLowRadius parameters L compact)

theorem radialForceKernel_one (kind : Fin 2) :
    SameKernelEntries (radialForceKernel parameters L compact state outerRadialPoint kind 0)
      (actualForceBoundaryKernel parameters L state.rho state.epsilon state.field kind state.coefficientSmall) :=
  radialForceKernel_one_entry parameters L compact state kind

theorem radialRotatedForceKernel_one (kind : Fin 2) :
    SameKernelEntries (radialRotatedForceKernel parameters L compact state outerRadialPoint kind 0)
      (actualRotatedForceBoundaryKernel parameters L state.rho state.epsilon state.field kind state.coefficientSmall) :=
  radialRotatedForceKernel_one_entry parameters L compact state kind

private abbrev gaugeSmall := small.trans (min_le_left _ _ : radialFirstLowRadius parameters L compact ≤ _)

theorem radialGaugeDecodedKernel_one :
    SameKernelEntries (radialGaugeDecodedKernel parameters L compact state outerRadialPoint
      (gaugeSmall parameters L compact state small))
      (actualGaugeDecodedKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.gaugeSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) :=
  (radialGaugeQKernel_one parameters L compact state _).comp (sameEncodedJKernel _ _)

theorem radialEncodedE0Kernel_one :
    SameKernelEntries (radialEncodedE0Kernel parameters L compact state outerRadialPoint
      (gaugeSmall parameters L compact state small))
      (actualEncodedE0Kernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.gaugeSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) := by
  exact (sameConstantMatrixKernel _ _ _ _ _).comp
    ((sameScalarModeDiagonalKernel _ _ _ _ _ _).comp
      ((radialForceKernel_one parameters L compact state 0).comp
        (radialGaugeDecodedKernel_one parameters L compact state small)))

theorem radialEncodedE1Kernel_one :
    SameKernelEntries (radialEncodedE1Kernel parameters L compact state outerRadialPoint
      (gaugeSmall parameters L compact state small))
      (actualEncodedE1Kernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.gaugeSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) := by
  exact (sameConstantMatrixKernel _ _ _ _ _).comp
    ((sameScalarModeDiagonalKernel _ _ _ _ _ _).comp
      (((radialRotatedForceKernel_one parameters L compact state 0).comp
        (radialGaugeDecodedKernel_one parameters L compact state small)).add
        ((radialForceKernel_one parameters L compact state 0).comp
          (sameEncodedRotationKernel _ _))))

theorem radialEncodedE2Kernel_one :
    SameKernelEntries (radialEncodedE2Kernel parameters L compact state outerRadialPoint
      (gaugeSmall parameters L compact state small))
      (actualEncodedE2Kernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.gaugeSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) := by
  exact (sameConstantMatrixKernel _ _ _ _ _).comp
    ((sameScalarModeDiagonalKernel _ _ _ _ _ _).comp
      ((radialForceKernel_one parameters L compact state 1).comp
        (radialGaugeDecodedKernel_one parameters L compact state small)))

theorem radialEncodedPerturbationKernel_one :
    SameKernelEntries (radialEncodedPerturbationKernel parameters L compact state outerRadialPoint
      (gaugeSmall parameters L compact state small))
      (actualEncodedPerturbationKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.gaugeSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) :=
  (radialEncodedE0Kernel_one parameters L compact state small).add
    ((radialEncodedE1Kernel_one parameters L compact state small).add
      (radialEncodedE2Kernel_one parameters L compact state small))

theorem radialPreconditionedEncodedKernel_one :
    SameKernelEntries (radialPreconditionedEncodedKernel parameters L compact state outerRadialPoint
      (gaugeSmall parameters L compact state small))
      (actualPreconditionedEncodedPerturbationKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.gaugeSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) :=
  (sameConstantMatrixKernel _ _ _ _ _).comp
    (radialEncodedPerturbationKernel_one parameters L compact state small)

theorem radialEncodedFirstInverseKernel_one :
    SameKernelEntries (radialEncodedFirstInverseKernel parameters L compact state outerRadialPoint small)
      (actualEncodedFirstInverseKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.firstSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) := by
  unfold radialEncodedFirstInverseKernel actualEncodedFirstInverseKernel
  apply SameKernelEntries.comp _ (sameConstantMatrixKernel _ _ _ _ _)
  unfold radialEncodedIdentityInverseKernel actualEncodedIdentityInverseKernel
  apply SameKernelEntries.neg
  exact ((radialPreconditionedEncodedKernel_one parameters L compact state small).neg).negativeIdentityInverse
    _ _ _ _ _ _

theorem radialKnownQStarKernel_one :
    SameKernelEntries (radialKnownQStarKernel parameters L compact state outerRadialPoint
      (gaugeSmall parameters L compact state small))
      (actualKnownQStarKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.gaugeSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) :=
  (radialGaugeQKernel_one parameters L compact state _).comp
    ((sameConstantMatrixKernel _ _ _ _ _).comp (sameConstantMatrixKernel _ _ _ _ _))

theorem radialKnownRotatedQStarKernel_one :
    SameKernelEntries (radialKnownRotatedQStarKernel parameters outerRadialPoint)
      (actualKnownRotatedQStarKernel parameters) :=
  (sameConstantMatrixKernel _ _ _ _ _).comp (sameConstantMatrixKernel _ _ _ _ _)

theorem radialKnownD0Kernel_one :
    SameKernelEntries (radialKnownD0Kernel parameters L compact state outerRadialPoint
      (gaugeSmall parameters L compact state small))
      (actualKnownEncodedD0Kernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.gaugeSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) := by
  exact (sameConstantMatrixKernel _ _ _ _ _).comp
    (((sameScalarModeDiagonalKernel _ _ _ _ _ _).comp (sameConstantMatrixKernel _ _ _ _ _)).sub
      ((sameScalarModeDiagonalKernel _ _ _ _ _ _).comp
        ((radialForceKernel_one parameters L compact state 0).comp
          (radialKnownQStarKernel_one parameters L compact state small))))

theorem radialKnownD1Kernel_one :
    SameKernelEntries (radialKnownD1Kernel parameters L compact state outerRadialPoint
      (gaugeSmall parameters L compact state small))
      (actualKnownEncodedD1Kernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.gaugeSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) := by
  exact (sameConstantMatrixKernel _ _ _ _ _).comp
    ((sameConstantMatrixKernel _ _ _ _ _).sub
      ((sameScalarModeDiagonalKernel _ _ _ _ _ _).comp
        (((radialRotatedForceKernel_one parameters L compact state 0).comp
          (radialKnownQStarKernel_one parameters L compact state small)).add
          ((radialForceKernel_one parameters L compact state 0).comp
            (radialKnownRotatedQStarKernel_one parameters)))))

theorem radialKnownD2Kernel_one :
    SameKernelEntries (radialKnownD2Kernel parameters L compact state outerRadialPoint
      (gaugeSmall parameters L compact state small))
      (actualKnownEncodedD2Kernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.gaugeSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) := by
  exact (sameConstantMatrixKernel _ _ _ _ _).comp
    (((sameConstantMatrixKernel _ _ _ _ _).add
      ((sameConstantMatrixKernel _ _ _ _ _).smul _)).sub
      ((sameScalarModeDiagonalKernel _ _ _ _ _ _).comp
        ((radialForceKernel_one parameters L compact state 1).comp
          (radialKnownQStarKernel_one parameters L compact state small))))

theorem radialKnownEncodedDataKernel_one :
    SameKernelEntries (radialKnownEncodedDataKernel parameters L compact state outerRadialPoint
      (gaugeSmall parameters L compact state small))
      (actualKnownEncodedDataKernel parameters L state.rho state.alpha state.delta state.parameter
        state.epsilon compact state.field state.gaugeSmall state.compactNonnegative
        state.alphaSmall state.deltaSmall state.parameterSmall) :=
  (radialKnownD0Kernel_one parameters L compact state small).add
    ((radialKnownD1Kernel_one parameters L compact state small).add
      (radialKnownD2Kernel_one parameters L compact state small))

end Grad.AnnularReconstruction
