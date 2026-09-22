import AHS13SameSevenSlotForceChart

noncomputable section
set_option maxHeartbeats 2200000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
private abbrev rp := radialKernelParameters parameters r
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialFirstLowRadius parameters L compact)

/-- The literal AE17 data are exactly the sum of the existing AHP known and
unknown data actions. The apparent missing P in N1 is removed by its genuine R law. -/
theorem radialSevenForceData_eq (angular cell : ℕ)
    (mass : NegativeTrace (rp parameters r) angular cell 1)
    (input : SevenSlotTrace (rp parameters r) angular cell)
    (massMean : IsAngularMeanFree (rp parameters r) angular cell mass) :
    radialForceEncodedDataTrace parameters L compact state r (small.trans (min_le_left _ _)) angular cell
      (radialSevenFreeChart parameters r angular cell mass input)
      (radialSevenFreeChartRotation parameters r angular cell mass input)
      (input 2) (input 4) (input 5) (input 6) =
    fullNegativeKernelAction (rp parameters r) angular cell
      (radialUnknownNKernel parameters L compact state r small) mass +
    fullNegativeKernelAction (rp parameters r) angular cell
      (radialKnownEncodedDataKernel parameters L compact state r (small.trans (min_le_left _ _)))
      (sevenSlotFlatten (rp parameters r) angular cell input) := by
  have unknownDerivative := radialGaugeQKernel_derivative parameters L compact state r
    (small.trans (min_le_left _ _)) angular cell _ _
    (actualUnknownQAKernel_derivative (rp parameters r) angular cell mass massMean)
  have productLaw := radialForceKernel_derivative parameters L compact state r 0 angular cell _ _ unknownDerivative
  have projected := angularMeanFreeKernel_action_eq (rp parameters r) angular cell _ productLaw.meanFree
  unfold radialForceEncodedDataTrace radialForceDataZero radialForceDataOne radialForceDataTwo
  rw [radialSevenFreeChartRotation_first]
  simp only [radialSevenFreeChart, radialSevenFreeChartRotation,
    radialUnknownNKernel, radialUnknownN0Kernel, radialUnknownN1Kernel, radialUnknownN2Kernel,
    radialKnownEncodedDataKernel, radialKnownD0Kernel, radialKnownD1Kernel, radialKnownD2Kernel,
    radialUnknownGaugeQAKernel, radialKnownQStarKernel, radialKnownRotatedQStarKernel,
    fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    fullNegativeKernelAction_add, fullNegativeKernelAction_sub, fullNegativeKernelAction_neg,
    fullNegativeKernelAction_smul, fullNegativeKernelAction_identity, ContinuousLinearMap.id_apply,
    sevenInputSlotKernel_action, map_add, map_sub, map_neg, map_smul]
  have projectedExpanded := projected
  simp only [map_add] at projectedExpanded
  rw [map_add] at projected
  have paired := congrArg (fullNegativeKernelAction (rp parameters r) angular cell
    (secondCoordinateInjectionKernel (rp parameters r))) projected
  simp only [map_add] at paired
  rw [← paired]
  abel

/-- Applying the existing inverse to these exact data gives the same two
stored AHP encoded actions, before the mass coordinate is substituted. -/
theorem radialSevenEncodedTrace_eq_inverse (angular cell : ℕ)
    (mass : NegativeTrace (rp parameters r) angular cell 1)
    (input : SevenSlotTrace (rp parameters r) angular cell)
    (massMean : IsAngularMeanFree (rp parameters r) angular cell mass) :
    radialSevenEncodedTrace parameters L compact state r small angular cell mass input =
    fullNegativeKernelAction (rp parameters r) angular cell
      (radialEncodedFirstInverseKernel parameters L compact state r small)
      (radialForceEncodedDataTrace parameters L compact state r (small.trans (min_le_left _ _)) angular cell
        (radialSevenFreeChart parameters r angular cell mass input)
        (radialSevenFreeChartRotation parameters r angular cell mass input)
        (input 2) (input 4) (input 5) (input 6)) := by
  rw [radialSevenForceData_eq parameters L compact state r small angular cell mass input massMean]
  simp only [radialSevenEncodedTrace, radialUnknownWKernel, radialKnownWKernel,
    fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply, map_add]

end Grad.AnnularReconstruction
