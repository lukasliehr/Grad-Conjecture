import AHP22ActualRadialCorrectedFluxIdentity

noncomputable section
set_option maxHeartbeats 1800000

namespace Grad.AnnularReconstruction
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialMassLowRadius parameters L compact)
variable (angular cell : ℕ)
private abbrev rp := radialKernelParameters parameters r

/-- The reconstructed covariant returns the prescribed mean-free physical
flux, including every inhomogeneous source slot. -/
theorem radialNormalizedCovariantKernel_correctedFlux_eq
    (input : SevenSlotTrace (rp parameters r) angular cell)
    (flux : NegativeTrace (rp parameters r) angular cell 1)
    (fluxSupported : IsAngularMeanFree (rp parameters r) angular cell flux)
    (fluxDerivative : IsAngularDerivative (rp parameters r) angular cell flux (input 0))
    (scalarDerivative : IsAngularDerivative (rp parameters r) angular cell (input 3) (input 1)) :
    radialCorrectedFluxTrace parameters L compact state r angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialNormalizedCovariantKernel parameters L compact state r small)
        (sevenSlotFlatten (rp parameters r) angular cell input)) (input 3) = flux := by
  let mass := fullNegativeKernelAction (rp parameters r) angular cell
    (radialRecoveredMassKernel parameters L compact state r small)
    (sevenSlotFlatten (rp parameters r) angular cell input)
  have supported : IsAngularMeanFree (rp parameters r) angular cell mass :=
    radialRecoveredMassKernel_action_meanFree parameters L compact state r small
      angular cell input fluxDerivative.meanFree
  have derivative := radialPreMassCorrectedFlux_derivative parameters L compact state r
    (small.trans (min_le_left _ _)) angular cell mass input supported scalarDerivative
  have equation := congrArg
    (fun kernel => fullNegativeKernelAction (rp parameters r) angular cell kernel
      (sevenSlotFlatten (rp parameters r) angular cell input))
    (radialRecoveredMassKernel_solves parameters L compact state r small)
  simp only [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    fullKernelNegativeIdentityPerturbation, fullNegativeKernelAction_sub,
    fullNegativeKernelAction_identity, ContinuousLinearMap.id_apply,
    radialMassRightHandKernel, sevenInputSlotKernel_action] at equation
  change fullNegativeKernelAction (rp parameters r) angular cell _ mass - mass = input 0 - _ at equation
  rw [equation, sub_add_cancel] at derivative
  have equality := derivative.unique_meanFree fluxDerivative
    (radialCorrectedFluxTrace_meanFree parameters L compact state r angular cell _ _) fluxSupported
  simpa only [radialPreMassCovariantTrace, radialNormalizedCovariantKernel,
    fullNegativeKernelAction_add, fullNegativeKernelAction_comp,
    ContinuousLinearMap.comp_apply, mass] using equality

theorem radialMassInverseKernel_action_left (mass : NegativeTrace (rp parameters r) angular cell 1) :
    fullNegativeKernelAction (rp parameters r) angular cell
      (radialMassInverseKernel parameters L compact state r small)
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialMassPerturbationKernel parameters L compact state r (small.trans (min_le_left _ _))) mass - mass) = mass := by
  have equation := congrArg
    (fun kernel => fullNegativeKernelAction (rp parameters r) angular cell kernel mass)
    (radialMassInverseKernel_twoSided parameters L compact state r small).2
  simpa only [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    fullKernelNegativeIdentityPerturbation, fullNegativeKernelAction_sub,
    fullNegativeKernelAction_identity, ContinuousLinearMap.id_apply] using equation

/-- The converse extracts the genuine derivative of the same actual flux
and recovers A by the exact left inverse, retaining the four-term j-star. -/
theorem radialPreMassCorrectedFlux_recovers_mass
    (mass : NegativeTrace (rp parameters r) angular cell 1)
    (input : SevenSlotTrace (rp parameters r) angular cell)
    (massSupported : IsAngularMeanFree (rp parameters r) angular cell mass)
    (scalarDerivative : IsAngularDerivative (rp parameters r) angular cell (input 3) (input 1))
    (fluxDerivative : NegativeTrace (rp parameters r) angular cell 1)
    (extracted : IsAngularDerivative (rp parameters r) angular cell
      (radialCorrectedFluxTrace parameters L compact state r angular cell
        (radialPreMassCovariantTrace parameters L compact state r (small.trans (min_le_left _ _))
          angular cell mass input) (input 3)) fluxDerivative) :
    fullNegativeKernelAction (rp parameters r) angular cell
      (radialMassInverseKernel parameters L compact state r small)
      (fluxDerivative - fullNegativeKernelAction (rp parameters r) angular cell
        (radialKnownJStarKernel parameters L compact state r (small.trans (min_le_left _ _)))
        (sevenSlotFlatten (rp parameters r) angular cell input)) = mass := by
  have physical := radialPreMassCorrectedFlux_derivative parameters L compact state r
    (small.trans (min_le_left _ _)) angular cell mass input massSupported scalarDerivative
  have equality : fluxDerivative =
      fullNegativeKernelAction (rp parameters r) angular cell
        (radialMassPerturbationKernel parameters L compact state r (small.trans (min_le_left _ _))) mass - mass +
      fullNegativeKernelAction (rp parameters r) angular cell
        (radialKnownJStarKernel parameters L compact state r (small.trans (min_le_left _ _)))
        (sevenSlotFlatten (rp parameters r) angular cell input) := by
    apply NegativeTrace.ext_coefficient (rp parameters r) angular cell
    intro mode
    exact (extracted mode).trans (physical mode).symm
  rw [equality, add_sub_cancel_right]
  exact radialMassInverseKernel_action_left parameters L compact state r small angular cell mass

end Grad.AnnularReconstruction
