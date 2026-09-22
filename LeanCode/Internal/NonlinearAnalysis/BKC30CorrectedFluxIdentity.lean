import BKC29PhysicalFluxPrimitives
import BKC20PhysicalMomentFamilies

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Allocation

/-- The actual outer-circle AF3 flux, with sigma=-e1+delta-sigma and
kappa1=delta-sigma's second component. The circle radius is exactly one. -/
def actualCorrectedFluxTrace (parameters : PhaseParameters)
    (L rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (angular cell : ℕ) (covariant : NegativeTrace parameters angular cell 3)
    (scalar : NegativeTrace parameters angular cell 1) : NegativeTrace parameters angular cell 1 :=
  fullNegativeKernelAction parameters angular cell (angularMeanFreeKernel parameters 1)
    (-fullNegativeKernelAction parameters angular cell (coordinateProjectionKernel parameters 3 0) covariant +
      fullNegativeKernelAction parameters angular cell
        (actualSigmaBoundaryKernel parameters L rho epsilon field low) covariant +
      fullNegativeKernelAction parameters angular cell
        (actualSigmaComponentBoundaryKernel parameters L rho epsilon field low 1) scalar)

theorem actualCorrectedFluxTrace_meanFree (parameters : PhaseParameters)
    (L rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (angular cell : ℕ) (covariant : NegativeTrace parameters angular cell 3)
    (scalar : NegativeTrace parameters angular cell 1) :
    IsAngularMeanFree parameters angular cell
      (actualCorrectedFluxTrace parameters L rho epsilon field low angular cell covariant scalar) :=
  angularMeanFreeKernel_action_meanFree parameters angular cell _

/-- Genuine angular differentiation of AF3 using the literal original sigma
and kappa coefficient sequences. -/
theorem actualCorrectedFluxTrace_derivative (parameters : PhaseParameters)
    (L rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (angular cell : ℕ) (covariant rotated : NegativeTrace parameters angular cell 3)
    (scalar scalarRotation : NegativeTrace parameters angular cell 1)
    (covariantDerivative : IsAngularDerivative parameters angular cell covariant rotated)
    (scalarDerivative : IsAngularDerivative parameters angular cell scalar scalarRotation) :
    IsAngularDerivative parameters angular cell
      (actualCorrectedFluxTrace parameters L rho epsilon field low angular cell covariant scalar)
      (fullNegativeKernelAction parameters angular cell (angularMeanFreeKernel parameters 1)
        (-fullNegativeKernelAction parameters angular cell (coordinateProjectionKernel parameters 3 0) rotated +
          (fullNegativeKernelAction parameters angular cell
            (actualRotatedSigmaBoundaryKernel parameters L rho epsilon field low) covariant +
           fullNegativeKernelAction parameters angular cell
            (actualSigmaBoundaryKernel parameters L rho epsilon field low) rotated) +
          (fullNegativeKernelAction parameters angular cell
            (actualRotatedSigmaComponentBoundaryKernel parameters L rho epsilon field low 1) scalar +
           fullNegativeKernelAction parameters angular cell
            (actualSigmaComponentBoundaryKernel parameters L rho epsilon field low 1) scalarRotation))) := by
  have first := covariantDerivative.constantMatrix
    (Grad.GaugeCoefficients.Physical.Ledger.matrixUnit (0 : Fin 1) (0 : Fin 3))
  have sigma := actualSigmaBoundaryKernel_derivative parameters L rho epsilon field low
    angular cell covariant rotated covariantDerivative
  have kappa := actualSigmaComponentBoundaryKernel_derivative parameters L rho epsilon field low 1
    angular cell scalar scalarRotation scalarDerivative
  exact ((first.neg.add sigma).add kappa).scalarMode angularMeanFreeMultiplier 1
    angularMeanFreeMultiplier_norm_le

/-- The actual force-reconstructed covariant field before the mass coordinate
is chosen; the inhomogeneous seven-slot data are retained. -/
def actualPreMassCovariantTrace (parameters : PhaseParameters) (L compactRadius : ℝ)
    (state : BoundaryReconstructionState parameters L compactRadius) (angular cell : ℕ)
    (mass : NegativeTrace parameters angular cell 1) (input : SevenSlotTrace parameters angular cell) :
    NegativeTrace parameters angular cell 3 :=
  fullNegativeKernelAction parameters angular cell
    (actualUnknownUKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon
      compactRadius state.field state.firstSmall state.compactNonnegative state.alphaSmall
      state.deltaSmall state.parameterSmall) mass +
  fullNegativeKernelAction parameters angular cell
    (actualKnownAStarKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon
      compactRadius state.field state.firstSmall state.compactNonnegative state.alphaSmall
      state.deltaSmall state.parameterSmall) (sevenSlotFlatten parameters angular cell input)

/-- AF11--12 on the supported physical force reconstruction, using the actual
signed flux coefficient and the genuine angular derivative. -/
theorem actualPreMassCorrectedFlux_derivative (parameters : PhaseParameters) (L compactRadius : ℝ)
    (state : BoundaryReconstructionState parameters L compactRadius) (angular cell : ℕ)
    (mass : NegativeTrace parameters angular cell 1) (input : SevenSlotTrace parameters angular cell)
    (massSupported : IsAngularMeanFree parameters angular cell mass)
    (scalarDerivative : IsAngularDerivative parameters angular cell (input 3) (input 1)) :
    IsAngularDerivative parameters angular cell
      (actualCorrectedFluxTrace parameters L state.rho state.epsilon state.field state.coefficientSmall
        angular cell (actualPreMassCovariantTrace parameters L compactRadius state angular cell mass input) (input 3))
      (fullNegativeKernelAction parameters angular cell
        (actualMassPerturbationKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon
          compactRadius state.field state.firstSmall state.compactNonnegative state.alphaSmall
          state.deltaSmall state.parameterSmall) mass - mass +
       fullNegativeKernelAction parameters angular cell
        (actualKnownJStarKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon
          compactRadius state.field state.firstSmall state.compactNonnegative state.alphaSmall
          state.deltaSmall state.parameterSmall) (sevenSlotFlatten parameters angular cell input)) := by
  have unknown := actualUnknownUKernel_derivative parameters L state.rho state.alpha state.delta
    state.parameter state.epsilon compactRadius state.field state.firstSmall state.compactNonnegative
    state.alphaSmall state.deltaSmall state.parameterSmall angular cell mass massSupported
  have known := actualKnownAStarKernel_derivative parameters L state.rho state.alpha state.delta
    state.parameter state.epsilon compactRadius state.field state.firstSmall state.compactNonnegative
    state.alphaSmall state.deltaSmall state.parameterSmall angular cell input scalarDerivative
  have flux := actualCorrectedFluxTrace_derivative parameters L state.rho state.epsilon state.field
    state.coefficientSmall angular cell _ _ (input 3) (input 1) (unknown.add known) scalarDerivative
  change IsAngularDerivative parameters angular cell
    (actualCorrectedFluxTrace parameters L state.rho state.epsilon state.field state.coefficientSmall
      angular cell (actualPreMassCovariantTrace parameters L compactRadius state angular cell mass input) (input 3)) _ at flux
  simp only [map_add, actualUnknownVKernel_first, actualKnownRAStarKernel_first, add_zero] at flux
  convert flux using 1
  unfold actualMassPerturbationKernel actualKnownJStarKernel
  simp only [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    fullNegativeKernelAction_add, sevenInputSlotKernel_action, map_add, map_neg,
    angularMeanFreeKernel_action_eq parameters angular cell mass massSupported]
  abel

/-- AF12's outer projection on T does not change the literal unprojected
expression: it is the genuine derivative of delta-sigma times U A. -/
theorem actualMassPerturbationKernel_unprojected
    (parameters : PhaseParameters) (L compactRadius : ℝ)
    (state : BoundaryReconstructionState parameters L compactRadius) (angular cell : ℕ)
    (mass : NegativeTrace parameters angular cell 1)
    (massSupported : IsAngularMeanFree parameters angular cell mass) :
    fullNegativeKernelAction parameters angular cell
      (actualMassPerturbationKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon
        compactRadius state.field state.firstSmall state.compactNonnegative state.alphaSmall
        state.deltaSmall state.parameterSmall) mass =
      fullNegativeKernelAction parameters angular cell
        (actualRotatedSigmaBoundaryKernel parameters L state.rho state.epsilon state.field state.coefficientSmall)
        (fullNegativeKernelAction parameters angular cell
          (actualUnknownUKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon
            compactRadius state.field state.firstSmall state.compactNonnegative state.alphaSmall
            state.deltaSmall state.parameterSmall) mass) +
      fullNegativeKernelAction parameters angular cell
        (actualSigmaBoundaryKernel parameters L state.rho state.epsilon state.field state.coefficientSmall)
        (fullNegativeKernelAction parameters angular cell
          (actualUnknownVKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon
            compactRadius state.field state.firstSmall state.compactNonnegative state.alphaSmall
            state.deltaSmall state.parameterSmall) mass) := by
  have unknown := actualUnknownUKernel_derivative parameters L state.rho state.alpha state.delta
    state.parameter state.epsilon compactRadius state.field state.firstSmall state.compactNonnegative
    state.alphaSmall state.deltaSmall state.parameterSmall angular cell mass massSupported
  have derivative := actualSigmaBoundaryKernel_derivative parameters L state.rho state.epsilon state.field
    state.coefficientSmall angular cell _ _ unknown
  unfold actualMassPerturbationKernel
  simp only [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply, fullNegativeKernelAction_add]
  exact angularMeanFreeKernel_action_eq parameters angular cell _ derivative.meanFree

/-- The actual known j* equals AF12's unprojected four-term expression.
Its mean-free property is derived from genuine sigma/kappa product rules. -/
theorem actualKnownJStarKernel_unprojected
    (parameters : PhaseParameters) (L compactRadius : ℝ)
    (state : BoundaryReconstructionState parameters L compactRadius) (angular cell : ℕ)
    (input : SevenSlotTrace parameters angular cell)
    (scalarDerivative : IsAngularDerivative parameters angular cell (input 3) (input 1)) :
    fullNegativeKernelAction parameters angular cell
      (actualKnownJStarKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon
        compactRadius state.field state.firstSmall state.compactNonnegative state.alphaSmall
        state.deltaSmall state.parameterSmall) (sevenSlotFlatten parameters angular cell input) =
      (fullNegativeKernelAction parameters angular cell
        (actualRotatedSigmaBoundaryKernel parameters L state.rho state.epsilon state.field state.coefficientSmall)
        (fullNegativeKernelAction parameters angular cell
          (actualKnownAStarKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon
            compactRadius state.field state.firstSmall state.compactNonnegative state.alphaSmall
            state.deltaSmall state.parameterSmall) (sevenSlotFlatten parameters angular cell input)) +
       fullNegativeKernelAction parameters angular cell
        (actualSigmaBoundaryKernel parameters L state.rho state.epsilon state.field state.coefficientSmall)
        (fullNegativeKernelAction parameters angular cell
          (actualKnownRAStarKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon
            compactRadius state.field state.firstSmall state.compactNonnegative state.alphaSmall
            state.deltaSmall state.parameterSmall) (sevenSlotFlatten parameters angular cell input))) +
      (fullNegativeKernelAction parameters angular cell
        (actualRotatedSigmaComponentBoundaryKernel parameters L state.rho state.epsilon state.field state.coefficientSmall 1)
        (input 3) +
       fullNegativeKernelAction parameters angular cell
        (actualSigmaComponentBoundaryKernel parameters L state.rho state.epsilon state.field state.coefficientSmall 1)
        (input 1)) := by
  have known := actualKnownAStarKernel_derivative parameters L state.rho state.alpha state.delta
    state.parameter state.epsilon compactRadius state.field state.firstSmall state.compactNonnegative
    state.alphaSmall state.deltaSmall state.parameterSmall angular cell input scalarDerivative
  have sigma := actualSigmaBoundaryKernel_derivative parameters L state.rho state.epsilon state.field
    state.coefficientSmall angular cell _ _ known
  have kappa := actualSigmaComponentBoundaryKernel_derivative parameters L state.rho state.epsilon state.field
    state.coefficientSmall 1 angular cell (input 3) (input 1) scalarDerivative
  unfold actualKnownJStarKernel
  simp only [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    fullNegativeKernelAction_add, sevenInputSlotKernel_action]
  exact angularMeanFreeKernel_action_eq parameters angular cell _ (sigma.add kappa).meanFree

end Grad.BoundaryKernelAction
