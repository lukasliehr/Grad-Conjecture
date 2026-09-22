import BKC30CorrectedFluxIdentity

noncomputable section

set_option maxHeartbeats 1200000

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compactRadius : ℝ)
    (state : BoundaryReconstructionState parameters L compactRadius) (angular cell : ℕ)

/-- The actual left mass inverse, on the same single base ball as the right
inverse. No angular or cell multiplier is inverted in this identity. -/
theorem actualMassInverseKernel_left :
    fullKernelComposition
      (actualMassInverseKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon
        compactRadius state.field state.small state.compactNonnegative state.alphaSmall
        state.deltaSmall state.parameterSmall)
      (fullKernelNegativeIdentityPerturbation parameters
        (actualMassPerturbationKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon
          compactRadius state.field state.firstSmall state.compactNonnegative state.alphaSmall
          state.deltaSmall state.parameterSmall)) = fullIdentityKernel parameters 1 := by
  unfold actualMassInverseKernel
  exact fullKernelNegativeIdentity_inverse_left parameters _ (1 / 2)
    (actualMassPerturbationKernel_moment_zero_le_half parameters L state.rho state.alpha state.delta
      state.parameter state.epsilon compactRadius state.field state.small state.compactNonnegative
      state.alphaSmall state.deltaSmall state.parameterSmall) (by norm_num)

theorem actualMassInverseKernel_action_left (mass : NegativeTrace parameters angular cell 1) :
    fullNegativeKernelAction parameters angular cell
      (actualMassInverseKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon
        compactRadius state.field state.small state.compactNonnegative state.alphaSmall
        state.deltaSmall state.parameterSmall)
      (fullNegativeKernelAction parameters angular cell
        (actualMassPerturbationKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon
          compactRadius state.field state.firstSmall state.compactNonnegative state.alphaSmall
          state.deltaSmall state.parameterSmall) mass - mass) = mass := by
  have identity := congrArg
    (fun kernel => fullNegativeKernelAction parameters angular cell kernel mass)
    (actualMassInverseKernel_left parameters L compactRadius state)
  simpa only [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    fullKernelNegativeIdentityPerturbation, fullNegativeKernelAction_sub,
    fullNegativeKernelAction_identity, ContinuousLinearMap.id_apply] using identity

/-- The mean-free first coordinate of the physical force reconstruction is
exactly alpha=K A. This is obtained from the genuine first-component
derivative and KR=P, including the angular constant part of the known field. -/
theorem actualPreMassCovariantTrace_alpha
    (mass : NegativeTrace parameters angular cell 1) (input : SevenSlotTrace parameters angular cell)
    (massSupported : IsAngularMeanFree parameters angular cell mass)
    (scalarDerivative : IsAngularDerivative parameters angular cell (input 3) (input 1)) :
    fullNegativeKernelAction parameters angular cell (angularMeanFreeKernel parameters 1)
      (fullNegativeKernelAction parameters angular cell (coordinateProjectionKernel parameters 3 0)
        (actualPreMassCovariantTrace parameters L compactRadius state angular cell mass input)) =
      fullNegativeKernelAction parameters angular cell (angularInverseKernel parameters 1) mass := by
  have unknown := actualUnknownUKernel_derivative parameters L state.rho state.alpha state.delta
    state.parameter state.epsilon compactRadius state.field state.firstSmall state.compactNonnegative
    state.alphaSmall state.deltaSmall state.parameterSmall angular cell mass massSupported
  have known := actualKnownAStarKernel_derivative parameters L state.rho state.alpha state.delta
    state.parameter state.epsilon compactRadius state.field state.firstSmall state.compactNonnegative
    state.alphaSmall state.deltaSmall state.parameterSmall angular cell input scalarDerivative
  have first := (unknown.add known).constantMatrix
    (Grad.GaugeCoefficients.Physical.Ledger.matrixUnit (0 : Fin 1) (0 : Fin 3))
  change IsAngularDerivative parameters angular cell
    (fullNegativeKernelAction parameters angular cell (coordinateProjectionKernel parameters 3 0)
      (actualPreMassCovariantTrace parameters L compactRadius state angular cell mass input))
    (fullNegativeKernelAction parameters angular cell (coordinateProjectionKernel parameters 3 0) _) at first
  simp only [map_add, actualUnknownVKernel_first, actualKnownRAStarKernel_first, add_zero] at first
  exact (first.meanFreeProjection.primitive
    (angularMeanFreeKernel_action_meanFree parameters angular cell _)).symm

/-- AF16 reconstructs exactly the prescribed mean-free physical corrected
flux, including the inhomogeneous dependence on the retained source slots. -/
theorem actualCovariantKernel_correctedFlux_eq
    (input : SevenSlotTrace parameters angular cell)
    (flux : NegativeTrace parameters angular cell 1)
    (fluxSupported : IsAngularMeanFree parameters angular cell flux)
    (fluxDerivative : IsAngularDerivative parameters angular cell flux (input 0))
    (scalarDerivative : IsAngularDerivative parameters angular cell (input 3) (input 1)) :
    actualCorrectedFluxTrace parameters L state.rho state.epsilon state.field state.coefficientSmall
      angular cell
      (fullNegativeKernelAction parameters angular cell
        (actualCovariantKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon
          compactRadius state.field state.small state.compactNonnegative state.alphaSmall
          state.deltaSmall state.parameterSmall) (sevenSlotFlatten parameters angular cell input))
      (input 3) = flux := by
  let mass := fullNegativeKernelAction parameters angular cell
    (actualRecoveredMassKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon
      compactRadius state.field state.small state.compactNonnegative state.alphaSmall
      state.deltaSmall state.parameterSmall) (sevenSlotFlatten parameters angular cell input)
  have supported : IsAngularMeanFree parameters angular cell mass :=
    actualRecoveredMassKernel_action_meanFree parameters L state.rho state.alpha state.delta
      state.parameter state.epsilon compactRadius state.field state.small state.compactNonnegative
      state.alphaSmall state.deltaSmall state.parameterSmall angular cell input fluxDerivative.meanFree
  have derivative := actualPreMassCorrectedFlux_derivative parameters L compactRadius state
    angular cell mass input supported scalarDerivative
  have equation := congrArg
    (fun kernel => fullNegativeKernelAction parameters angular cell kernel
      (sevenSlotFlatten parameters angular cell input))
    (actualRecoveredMassKernel_solves parameters L state.rho state.alpha state.delta state.parameter
      state.epsilon compactRadius state.field state.small state.compactNonnegative state.alphaSmall
      state.deltaSmall state.parameterSmall)
  simp only [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    fullKernelNegativeIdentityPerturbation, fullNegativeKernelAction_sub,
    fullNegativeKernelAction_identity, ContinuousLinearMap.id_apply,
    actualMassRightHandKernel, sevenInputSlotKernel_action] at equation
  change fullNegativeKernelAction parameters angular cell _ mass - mass = input 0 - _ at equation
  rw [equation, sub_add_cancel] at derivative
  have equality := derivative.unique_meanFree fluxDerivative
    (actualCorrectedFluxTrace_meanFree parameters L state.rho state.epsilon state.field
      state.coefficientSmall angular cell _ _) fluxSupported
  simpa only [actualPreMassCovariantTrace, actualCovariantKernel,
    fullNegativeKernelAction_add, fullNegativeKernelAction_comp,
    ContinuousLinearMap.comp_apply, mass] using equality

/-- Conversely, extracting the genuine angular derivative of the actual
corrected flux and applying AF16 recovers the original encoded mass A. -/
theorem actualPreMassCorrectedFlux_recovers_mass
    (mass : NegativeTrace parameters angular cell 1) (input : SevenSlotTrace parameters angular cell)
    (massSupported : IsAngularMeanFree parameters angular cell mass)
    (scalarDerivative : IsAngularDerivative parameters angular cell (input 3) (input 1))
    (fluxDerivative : NegativeTrace parameters angular cell 1)
    (extracted : IsAngularDerivative parameters angular cell
      (actualCorrectedFluxTrace parameters L state.rho state.epsilon state.field state.coefficientSmall
        angular cell (actualPreMassCovariantTrace parameters L compactRadius state angular cell mass input) (input 3))
      fluxDerivative) :
    fullNegativeKernelAction parameters angular cell
      (actualMassInverseKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon
        compactRadius state.field state.small state.compactNonnegative state.alphaSmall
        state.deltaSmall state.parameterSmall)
      (fluxDerivative - fullNegativeKernelAction parameters angular cell
        (actualKnownJStarKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon
          compactRadius state.field state.firstSmall state.compactNonnegative state.alphaSmall
          state.deltaSmall state.parameterSmall) (sevenSlotFlatten parameters angular cell input)) = mass := by
  have physical := actualPreMassCorrectedFlux_derivative parameters L compactRadius state
    angular cell mass input massSupported scalarDerivative
  have equality : fluxDerivative =
      fullNegativeKernelAction parameters angular cell
        (actualMassPerturbationKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon
          compactRadius state.field state.firstSmall state.compactNonnegative state.alphaSmall
          state.deltaSmall state.parameterSmall) mass - mass +
       fullNegativeKernelAction parameters angular cell
        (actualKnownJStarKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon
          compactRadius state.field state.firstSmall state.compactNonnegative state.alphaSmall
          state.deltaSmall state.parameterSmall) (sevenSlotFlatten parameters angular cell input) := by
    apply NegativeTrace.ext_coefficient parameters angular cell
    intro mode
    exact (extracted mode).trans (physical mode).symm
  rw [equality, add_sub_cancel_right]
  exact actualMassInverseKernel_action_left parameters L compactRadius state angular cell mass

/-- The same physical converse recovers alpha=K A, not merely its derivative. -/
theorem actualPreMassCorrectedFlux_recovers_alpha
    (mass : NegativeTrace parameters angular cell 1) (input : SevenSlotTrace parameters angular cell)
    (massSupported : IsAngularMeanFree parameters angular cell mass)
    (scalarDerivative : IsAngularDerivative parameters angular cell (input 3) (input 1))
    (fluxDerivative : NegativeTrace parameters angular cell 1)
    (extracted : IsAngularDerivative parameters angular cell
      (actualCorrectedFluxTrace parameters L state.rho state.epsilon state.field state.coefficientSmall
        angular cell (actualPreMassCovariantTrace parameters L compactRadius state angular cell mass input) (input 3))
      fluxDerivative) :
    fullNegativeKernelAction parameters angular cell (angularInverseKernel parameters 1)
      (fullNegativeKernelAction parameters angular cell
        (actualMassInverseKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon
          compactRadius state.field state.small state.compactNonnegative state.alphaSmall
          state.deltaSmall state.parameterSmall)
        (fluxDerivative - fullNegativeKernelAction parameters angular cell
          (actualKnownJStarKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon
            compactRadius state.field state.firstSmall state.compactNonnegative state.alphaSmall
            state.deltaSmall state.parameterSmall) (sevenSlotFlatten parameters angular cell input))) =
      fullNegativeKernelAction parameters angular cell (angularInverseKernel parameters 1) mass := by
  rw [actualPreMassCorrectedFlux_recovers_mass parameters L compactRadius state angular cell
    mass input massSupported scalarDerivative fluxDerivative extracted]

end Grad.BoundaryKernelAction
