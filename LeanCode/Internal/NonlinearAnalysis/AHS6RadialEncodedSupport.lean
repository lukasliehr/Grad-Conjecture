import AHS5ActualCovariantGaugeConsumer

noncomputable section
set_option maxHeartbeats 1800000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
private abbrev rp := radialKernelParameters parameters r

section Gauge
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialGaugeLowRadius parameters L compact)

theorem radialEncodedPerturbationKernel_support (angular cell : ℕ)
    (input : NegativeTrace (rp parameters r) angular cell 3) :
    EncodedSupport (rp parameters r) angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialEncodedPerturbationKernel parameters L compact state r small) input) := by
  unfold radialEncodedPerturbationKernel
  rw [fullNegativeKernelAction_add, fullNegativeKernelAction_add]
  apply EncodedSupport.add
  · unfold radialEncodedE0Kernel firstCoordinateInjectionKernel
    rw [fullNegativeKernelAction_comp]
    apply coordinateInjectionKernel_action_encoded_zero
    rw [fullNegativeKernelAction_comp]
    exact angularMeanKernel_action_constant _ _ _ _
  · apply EncodedSupport.add
    · unfold radialEncodedE1Kernel secondCoordinateInjectionKernel
      rw [fullNegativeKernelAction_comp]
      apply coordinateInjectionKernel_action_encoded_one
      rw [fullNegativeKernelAction_comp]
      exact angularMeanFreeKernel_action_meanFree _ _ _ _
    · unfold radialEncodedE2Kernel thirdCoordinateInjectionKernel
      rw [fullNegativeKernelAction_comp]
      apply coordinateInjectionKernel_action_encoded_two
      rw [fullNegativeKernelAction_comp]
      exact angularMeanFreeKernel_action_meanFree _ _ _ _
end Gauge

section First
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialFirstLowRadius parameters L compact)

theorem radialEncodedFirstInverseKernel_support (angular cell : ℕ)
    (input : NegativeTrace (rp parameters r) angular cell 3)
    (supported : EncodedSupport (rp parameters r) angular cell input) :
    EncodedSupport (rp parameters r) angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialEncodedFirstInverseKernel parameters L compact state r small) input) := by
  unfold radialEncodedFirstInverseKernel
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  apply fullPositiveIdentityInverse_action_support (rp parameters r) angular cell
    (EncodedSupport (rp parameters r) angular cell) (fun first second => first.sub second)
    _ _ (radialEncodedIdentityInverseKernel_right parameters L compact state r small)
    _ _ (encodedD0InverseKernel_action_support (rp parameters r) angular cell input supported)
  intro argument
  unfold radialPreconditionedEncodedKernel
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply]
  apply encodedD0InverseKernel_action_support
  exact radialEncodedPerturbationKernel_support parameters L compact state r
    (small.trans (min_le_left _ _)) angular cell argument
end First

/-- Mean and genuine angular derivative determine a completed field exactly;
there is no lost first-row equation at angular frequency zero. -/
theorem angularDerivative_equal_iff_mean_derivative {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (first second firstDerivative secondDerivative : NegativeTrace parameters angular cell dimension)
    (firstLaw : IsAngularDerivative parameters angular cell first firstDerivative)
    (secondLaw : IsAngularDerivative parameters angular cell second secondDerivative) :
    first = second ↔
      fullNegativeKernelAction parameters angular cell (angularMeanKernel parameters dimension) first =
        fullNegativeKernelAction parameters angular cell (angularMeanKernel parameters dimension) second ∧
      firstDerivative = secondDerivative := by
  constructor
  · intro same
    subst second
    refine ⟨rfl, ?_⟩
    apply NegativeTrace.ext_coefficient parameters angular cell
    intro mode
    rw [firstLaw, secondLaw]
  · rintro ⟨means, derivatives⟩
    apply NegativeTrace.ext_coefficient parameters angular cell
    intro mode
    by_cases zero : mode.1 = 0
    · have evaluated := congrArg (fun field => negativeTraceCoefficient parameters angular cell field mode) means
      simpa [angularMeanKernel, scalarModeDiagonalKernel_action_coefficient,
        angularMeanMultiplier, zero] using evaluated
    · have evaluated := congrArg (fun field => negativeTraceCoefficient parameters angular cell field mode) derivatives
      rw [firstLaw, secondLaw] at evaluated
      exact (smul_right_injective _ (mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr zero))) evaluated

end Grad.AnnularReconstruction
