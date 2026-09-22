import AHS15SameCovariantPhysicalForceRows

noncomputable section
set_option maxHeartbeats 1800000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialMassLowRadius parameters L compact)
private abbrev rp := radialKernelParameters parameters r

 theorem radialNormalizedCovariant_force_rows (angular cell : ℕ)
    (input : SevenSlotTrace (rp parameters r) angular cell)
    (massMean : IsAngularMeanFree (rp parameters r) angular cell (input 0))
    (scalarLaw : IsAngularDerivative (rp parameters r) angular cell (input 3) (input 1))
    (sourceLaw : IsAngularDerivative (rp parameters r) angular cell (input 4) (input 5))
    (xiZetaMean : IsAngularMeanFree (rp parameters r) angular cell (input 2))
    (sourceTwoMean : IsAngularMeanFree (rp parameters r) angular cell (input 6)) :
    let covariant := fullNegativeKernelAction (rp parameters r) angular cell
      (radialNormalizedCovariantKernel parameters L compact state r small)
      (sevenSlotFlatten (rp parameters r) angular cell input)
    let rotated := fullNegativeKernelAction (rp parameters r) angular cell
      (radialNormalizedRotatedCovariantKernel parameters L compact state r small)
      (sevenSlotFlatten (rp parameters r) angular cell input)
    (-forceCoordinateTrace (rp parameters r) angular cell 1 rotated -
      (2 : ℂ) • forceCoordinateTrace (rp parameters r) angular cell 0 covariant +
      fullNegativeKernelAction (rp parameters r) angular cell (radialForceKernel parameters L compact state r 0 0) covariant +
      input 1 = input 4) ∧
    (forceCoordinateTrace (rp parameters r) angular cell 2 rotated +
      forceMeanFreeTrace (rp parameters r) angular cell
        (fullNegativeKernelAction (rp parameters r) angular cell (radialForceKernel parameters L compact state r 1 0) covariant) -
      (L : ℂ)⁻¹ • input 2 = input 6) := by
  dsimp only
  simp only [radialNormalizedCovariantKernel, radialNormalizedRotatedCovariantKernel,
    fullNegativeKernelAction_add, fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  exact radialSevenCovariant_force_rows parameters L compact state r (small.trans (min_le_left _ _)) angular cell
    _ input (radialRecoveredMassKernel_action_meanFree parameters L compact state r small angular cell input massMean)
    scalarLaw sourceLaw xiZetaMean sourceTwoMean

/-- All positive-radius AD9 first/third rows for the same original seven-slot
reconstruction, with literal -2a1, +r^-1 Rxi, and -L^-1 xi_zeta. -/
theorem radialOriginalCovariant_force_rows (positive : 0 < r.val) (angular cell : ℕ)
    (input : SevenSlotTrace (rp parameters r) angular cell)
    (massMean : IsAngularMeanFree (rp parameters r) angular cell (input 0))
    (scalarLaw : IsAngularDerivative (rp parameters r) angular cell (input 3) (input 1))
    (sourceLaw : IsAngularDerivative (rp parameters r) angular cell (input 4) (input 5))
    (xiZetaMean : IsAngularMeanFree (rp parameters r) angular cell (input 2))
    (sourceTwoMean : IsAngularMeanFree (rp parameters r) angular cell (input 6)) :
    let covariant := fullNegativeKernelAction (rp parameters r) angular cell
      (radialCovariantKernel parameters L compact state r small positive)
      (sevenSlotFlatten (rp parameters r) angular cell input)
    let rotated := fullNegativeKernelAction (rp parameters r) angular cell
      (radialRotatedCovariantKernel parameters L compact state r small positive)
      (sevenSlotFlatten (rp parameters r) angular cell input)
    (-forceCoordinateTrace (rp parameters r) angular cell 1 rotated -
      (2 : ℂ) • forceCoordinateTrace (rp parameters r) angular cell 0 covariant +
      fullNegativeKernelAction (rp parameters r) angular cell (radialForceKernel parameters L compact state r 0 0) covariant +
      (r.val : ℂ)⁻¹ • input 1 = input 4) ∧
    (forceCoordinateTrace (rp parameters r) angular cell 2 rotated +
      forceMeanFreeTrace (rp parameters r) angular cell
        (fullNegativeKernelAction (rp parameters r) angular cell (radialForceKernel parameters L compact state r 1 0) covariant) -
      (L : ℂ)⁻¹ • input 2 = input 6) := by
  dsimp only
  simp only [radialCovariantKernel, radialRotatedCovariantKernel,
    fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply, radialSevenSlotKernel_action]
  exact radialNormalizedCovariant_force_rows parameters L compact state r small angular cell
    (radialNormalizedSevenInput parameters r angular cell input) massMean
    (radialNormalizedSevenInput_derivative parameters r angular cell input scalarLaw)
    sourceLaw xiZetaMean sourceTwoMean

/-- Exact physical consumer: original coefficients, original seven slots,
both actual gauges, genuine R, and both force equations at every positive radius. -/
theorem actualRadialForceGaugeConsumer (positive : 0 < r.val) (angular cell : ℕ)
    (input : SevenSlotTrace (rp parameters r) angular cell)
    (massMean : IsAngularMeanFree (rp parameters r) angular cell (input 0))
    (scalarMean : IsAngularMeanFree (rp parameters r) angular cell (input 3))
    (scalarLaw : IsAngularDerivative (rp parameters r) angular cell (input 3) (input 1))
    (sourceLaw : IsAngularDerivative (rp parameters r) angular cell (input 4) (input 5))
    (xiZetaMean : IsAngularMeanFree (rp parameters r) angular cell (input 2))
    (sourceTwoMean : IsAngularMeanFree (rp parameters r) angular cell (input 6)) :
    let covariant := fullNegativeKernelAction (rp parameters r) angular cell
      (radialCovariantKernel parameters L compact state r small positive)
      (sevenSlotFlatten (rp parameters r) angular cell input)
    let rotated := fullNegativeKernelAction (rp parameters r) angular cell
      (radialRotatedCovariantKernel parameters L compact state r small positive)
      (sevenSlotFlatten (rp parameters r) angular cell input)
    radialPhysicalGaugeMeans parameters L compact state r angular cell covariant = 0 ∧
    IsAngularDerivative (rp parameters r) angular cell covariant rotated ∧
    (-forceCoordinateTrace (rp parameters r) angular cell 1 rotated -
      (2 : ℂ) • forceCoordinateTrace (rp parameters r) angular cell 0 covariant +
      fullNegativeKernelAction (rp parameters r) angular cell (radialForceKernel parameters L compact state r 0 0) covariant +
      (r.val : ℂ)⁻¹ • input 1 = input 4) ∧
    (forceCoordinateTrace (rp parameters r) angular cell 2 rotated +
      forceMeanFreeTrace (rp parameters r) angular cell
        (fullNegativeKernelAction (rp parameters r) angular cell (radialForceKernel parameters L compact state r 1 0) covariant) -
      (L : ℂ)⁻¹ • input 2 = input 6) :=
  ⟨radialCovariantKernel_gauged parameters L compact state r small positive angular cell input scalarMean,
   radialCovariantKernel_derivative parameters L compact state r small positive angular cell input massMean scalarLaw,
   radialOriginalCovariant_force_rows parameters L compact state r small positive angular cell input massMean
     scalarLaw sourceLaw xiZetaMean sourceTwoMean⟩

end Grad.AnnularReconstruction
