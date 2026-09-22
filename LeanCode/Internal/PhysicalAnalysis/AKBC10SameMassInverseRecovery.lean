import AKBC9SameForceInverseRecovery

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7≤
  radialMassLowRadius parameters L compact) (angular cell : ℕ)
private abbrev rp := radialKernelParameters parameters r

/-- The genuine derivative of the same original corrected flux selects the
already constructed mass inverse and consequently the same full covariant. -/
theorem originalCovariant_massRecovery (field : NegativeTrace (rp parameters r) angular cell 3)
    (mass : NegativeTrace (rp parameters r) angular cell 1)
    (input : SevenSlotTrace (rp parameters r) angular cell)
    (massMean : IsAngularMeanFree (rp parameters r) angular cell mass)
    (scalarRotation : IsAngularDerivative (rp parameters r) angular cell (input 3) (input 1))
    (preMass : field=radialPreMassCovariantTrace parameters L compact state r
      (small.trans (min_le_left _ _)) angular cell mass input)
    (fluxRotation : IsAngularDerivative (rp parameters r) angular cell
      (radialCorrectedFluxTrace parameters L compact state r angular cell field (input 3)) (input 0)) :
    field=fullNegativeKernelAction (rp parameters r) angular cell
      (radialNormalizedCovariantKernel parameters L compact state r small)
      (sevenSlotFlatten (rp parameters r) angular cell input) := by
  have recovered := radialPreMassCorrectedFlux_recovers_mass parameters L compact state r small angular cell
    mass input massMean scalarRotation (input 0) (by rw [← preMass]; exact fluxRotation)
  have recoveredValue : fullNegativeKernelAction (rp parameters r) angular cell
      (radialRecoveredMassKernel parameters L compact state r small)
      (sevenSlotFlatten (rp parameters r) angular cell input)=mass := by
    simpa only [radialRecoveredMassKernel,radialMassRightHandKernel,fullNegativeKernelAction_comp,
      ContinuousLinearMap.comp_apply,fullNegativeKernelAction_sub,sevenInputSlotKernel_action] using recovered
  rw [radialNormalizedCovariantKernel,fullNegativeKernelAction_add,fullNegativeKernelAction_comp,
    ContinuousLinearMap.comp_apply,recoveredValue]
  exact preMass

end Grad.OriginalKernelCovariantRecovery
