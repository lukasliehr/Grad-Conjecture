import AHS11ActualEncodedForceSystem

noncomputable section
set_option maxHeartbeats 1800000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

private theorem angularMeanFree_smul_trace {dimension : ℕ} {parameters : PhaseParameters}
    {angular cell : ℕ} {field : NegativeTrace parameters angular cell dimension}
    (law : IsAngularMeanFree parameters angular cell field) (scalar : ℂ) :
    IsAngularMeanFree parameters angular cell (scalar • field) := by
  intro axial
  rw [negativeTraceCoefficient_smul, law, smul_zero]

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
private abbrev rp := radialKernelParameters parameters r

 theorem radialForceEncodedDataTrace_support
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
      radialGaugeLowRadius parameters L compact) (angular cell : ℕ)
    (known knownDerivative : NegativeTrace (rp parameters r) angular cell 3)
    (xiZeta sourceZero sourceDerivative sourceTwo : NegativeTrace (rp parameters r) angular cell 1)
    (knownLaw : IsAngularDerivative (rp parameters r) angular cell known knownDerivative)
    (sourceLaw : IsAngularDerivative (rp parameters r) angular cell sourceZero sourceDerivative)
    (xiZetaMean : IsAngularMeanFree (rp parameters r) angular cell xiZeta)
    (sourceTwoMean : IsAngularMeanFree (rp parameters r) angular cell sourceTwo) :
    EncodedSupport (rp parameters r) angular cell
      (radialForceEncodedDataTrace parameters L compact state r small angular cell
        known knownDerivative xiZeta sourceZero sourceDerivative sourceTwo) := by
  unfold radialForceEncodedDataTrace
  apply EncodedSupport.add
  · unfold firstCoordinateInjectionKernel
    apply coordinateInjectionKernel_action_encoded_zero
    exact (angularMeanKernel_action_constant _ _ _ _).sub (angularMeanKernel_action_constant _ _ _ _)
  · apply EncodedSupport.add
    · unfold secondCoordinateInjectionKernel
      apply coordinateInjectionKernel_action_encoded_one
      apply (sourceLaw.meanFree.add (angularMeanFree_smul_trace
        (knownLaw.constantMatrix (matrixUnit 0 0)).meanFree 2)).sub
      exact angularMeanFreeKernel_action_meanFree _ _ _ _
    · unfold thirdCoordinateInjectionKernel
      apply coordinateInjectionKernel_action_encoded_two
      exact (sourceTwoMean.add (angularMeanFree_smul_trace xiZetaMean _)).sub
        (angularMeanFreeKernel_action_meanFree _ _ _ _)

/-- The existing AHP inverse actually solves both literal force rows at
all radii, for the original source support and genuine angular derivatives. -/
theorem radialEncodedFirstInverse_solves_force
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
      radialFirstLowRadius parameters L compact) (angular cell : ℕ)
    (known knownDerivative : NegativeTrace (rp parameters r) angular cell 3)
    (xiZeta sourceZero sourceDerivative sourceTwo : NegativeTrace (rp parameters r) angular cell 1)
    (knownMean : IsAngularMeanFreeComponent (rp parameters r) angular cell 0 known)
    (knownLaw : IsAngularDerivative (rp parameters r) angular cell known knownDerivative)
    (sourceLaw : IsAngularDerivative (rp parameters r) angular cell sourceZero sourceDerivative)
    (xiZetaMean : IsAngularMeanFree (rp parameters r) angular cell xiZeta)
    (sourceTwoMean : IsAngularMeanFree (rp parameters r) angular cell sourceTwo) :
    let gaugeSmall := small.trans (min_le_left _ _)
    let data := radialForceEncodedDataTrace parameters L compact state r gaugeSmall angular cell
      known knownDerivative xiZeta sourceZero sourceDerivative sourceTwo
    let encoded := fullNegativeKernelAction (rp parameters r) angular cell
      (radialEncodedFirstInverseKernel parameters L compact state r small) data
    EncodedSupport (rp parameters r) angular cell encoded ∧
      radialFirstForceTrace parameters L compact state r gaugeSmall angular cell encoded known = sourceZero ∧
      radialThirdForceTrace parameters L compact state r gaugeSmall angular cell encoded known xiZeta = sourceTwo := by
  dsimp only
  have support := radialEncodedFirstInverseKernel_support parameters L compact state r small angular cell _
    (radialForceEncodedDataTrace_support parameters L compact state r (small.trans (min_le_left _ _))
      angular cell known knownDerivative xiZeta sourceZero sourceDerivative sourceTwo knownLaw sourceLaw xiZetaMean sourceTwoMean)
  refine ⟨support, ?_⟩
  apply (radialForceEncoding_system_iff parameters L compact state r small angular cell _
    known knownDerivative xiZeta sourceZero sourceDerivative sourceTwo support knownMean knownLaw sourceLaw).mpr
  rw [← ContinuousLinearMap.comp_apply, ← fullNegativeKernelAction_comp,
    (radialEncodedFirstInverseKernel_twoSided parameters L compact state r small).1,
    fullNegativeKernelAction_identity, ContinuousLinearMap.id_apply]

/-- Converse force constraints recover the same constructed encoded inverse. -/
theorem radialEncodedFirstInverse_force_unique
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
      radialFirstLowRadius parameters L compact) (angular cell : ℕ)
    (encoded known knownDerivative : NegativeTrace (rp parameters r) angular cell 3)
    (xiZeta sourceZero sourceDerivative sourceTwo : NegativeTrace (rp parameters r) angular cell 1)
    (supported : EncodedSupport (rp parameters r) angular cell encoded)
    (knownMean : IsAngularMeanFreeComponent (rp parameters r) angular cell 0 known)
    (knownLaw : IsAngularDerivative (rp parameters r) angular cell known knownDerivative)
    (sourceLaw : IsAngularDerivative (rp parameters r) angular cell sourceZero sourceDerivative)
    (forces : radialFirstForceTrace parameters L compact state r (small.trans (min_le_left _ _)) angular cell encoded known = sourceZero ∧
      radialThirdForceTrace parameters L compact state r (small.trans (min_le_left _ _)) angular cell encoded known xiZeta = sourceTwo) :
    encoded = fullNegativeKernelAction (rp parameters r) angular cell
      (radialEncodedFirstInverseKernel parameters L compact state r small)
      (radialForceEncodedDataTrace parameters L compact state r (small.trans (min_le_left _ _)) angular cell
        known knownDerivative xiZeta sourceZero sourceDerivative sourceTwo) := by
  have equation := (radialForceEncoding_system_iff parameters L compact state r small angular cell encoded
    known knownDerivative xiZeta sourceZero sourceDerivative sourceTwo supported knownMean knownLaw sourceLaw).mp forces
  have applied := congrArg (fullNegativeKernelAction (rp parameters r) angular cell
    (radialEncodedFirstInverseKernel parameters L compact state r small)) equation
  rw [← ContinuousLinearMap.comp_apply, ← fullNegativeKernelAction_comp,
    (radialEncodedFirstInverseKernel_twoSided parameters L compact state r small).2,
    fullNegativeKernelAction_identity, ContinuousLinearMap.id_apply] at applied
  exact applied

end Grad.AnnularReconstruction
