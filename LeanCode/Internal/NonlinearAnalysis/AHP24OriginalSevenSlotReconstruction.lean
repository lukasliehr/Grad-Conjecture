import AHP23RadialPhysicalCoordinateIdentities

noncomputable section
set_option maxHeartbeats 1800000

namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

private theorem angularDerivative_smul {dimension : ℕ} {parameters : PhaseParameters}
    {angular cell : ℕ} {field derivative : NegativeTrace parameters angular cell dimension}
    (h : IsAngularDerivative parameters angular cell field derivative) (scalar : ℂ) :
    IsAngularDerivative parameters angular cell (scalar • field) (scalar • derivative) := by
  intro mode
  rw [negativeTraceCoefficient_smul, negativeTraceCoefficient_smul, h mode]
  exact smul_comm _ _ _

/-- Normalize only the two physical xi/r slots. All prescribed source slots
remain exactly the original F0, RF0, and F2. -/
def radialNormalizedSevenInput (parameters : PhaseParameters) (r : RadialPoint)
    (angular cell : ℕ) (input : SevenSlotTrace (radialKernelParameters parameters r) angular cell) :
    SevenSlotTrace (radialKernelParameters parameters r) angular cell :=
  WithLp.toLp 2 ![input 0, (r.val : ℂ)⁻¹ • input 1, input 2,
    (r.val : ℂ)⁻¹ • input 3, input 4, input 5, input 6]

theorem radialSevenSlotKernel_action (parameters : PhaseParameters) (r : RadialPoint)
    (angular cell : ℕ) (input : SevenSlotTrace (radialKernelParameters parameters r) angular cell) :
    fullNegativeKernelAction (radialKernelParameters parameters r) angular cell
      (radialSevenSlotKernel parameters r)
      (sevenSlotFlatten (radialKernelParameters parameters r) angular cell input) =
    sevenSlotFlatten (radialKernelParameters parameters r) angular cell
      (radialNormalizedSevenInput parameters r angular cell input) := by
  apply NegativeTrace.ext_coefficient (radialKernelParameters parameters r) angular cell
  intro mode
  rw [radialSevenSlotKernel, constantMatrixKernel_action_coefficient, radialSevenSlotNormalization_apply]
  apply PiLp.ext
  intro component
  rw [sevenSlotFlatten_coefficient]
  fin_cases component <;>
    simp [radialNormalizedSevenInput, sevenSlotFlatten_coefficient]

theorem radialNormalizedSevenInput_derivative (parameters : PhaseParameters) (r : RadialPoint)
    (angular cell : ℕ) (input : SevenSlotTrace (radialKernelParameters parameters r) angular cell)
    (derivative : IsAngularDerivative (radialKernelParameters parameters r) angular cell (input 3) (input 1)) :
    IsAngularDerivative (radialKernelParameters parameters r) angular cell
      (radialNormalizedSevenInput parameters r angular cell input 3)
      (radialNormalizedSevenInput parameters r angular cell input 1) :=
  angularDerivative_smul derivative _

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialMassLowRadius parameters L compact)
variable (positive : 0 < r.val) (angular cell : ℕ)
private abbrev rp := radialKernelParameters parameters r

/-- AH20's full original seven-slot action has its genuine angular derivative
at each positive radius, with all full cell frequencies retained. -/
theorem radialCovariantKernel_derivative
    (input : SevenSlotTrace (rp parameters r) angular cell)
    (supported : IsAngularMeanFree (rp parameters r) angular cell (input 0))
    (scalarDerivative : IsAngularDerivative (rp parameters r) angular cell (input 3) (input 1)) :
    IsAngularDerivative (rp parameters r) angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialCovariantKernel parameters L compact state r small positive)
        (sevenSlotFlatten (rp parameters r) angular cell input))
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialRotatedCovariantKernel parameters L compact state r small positive)
        (sevenSlotFlatten (rp parameters r) angular cell input)) := by
  unfold radialCovariantKernel radialRotatedCovariantKernel
  rw [fullNegativeKernelAction_comp, fullNegativeKernelAction_comp,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, radialSevenSlotKernel_action]
  exact radialNormalizedCovariantKernel_derivative parameters L compact state r small
    angular cell _ supported (radialNormalizedSevenInput_derivative parameters r angular cell input scalarDerivative)

/-- The original seven-input reconstruction has exactly the actual physical
flux P[sigma a + kappa1 xi/r], with the original radial factor and sign. -/
theorem radialCovariantKernel_correctedFlux_eq
    (input : SevenSlotTrace (rp parameters r) angular cell)
    (flux : NegativeTrace (rp parameters r) angular cell 1)
    (fluxSupported : IsAngularMeanFree (rp parameters r) angular cell flux)
    (fluxDerivative : IsAngularDerivative (rp parameters r) angular cell flux (input 0))
    (scalarDerivative : IsAngularDerivative (rp parameters r) angular cell (input 3) (input 1)) :
    radialCorrectedFluxTrace parameters L compact state r angular cell
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialCovariantKernel parameters L compact state r small positive)
        (sevenSlotFlatten (rp parameters r) angular cell input))
      ((r.val : ℂ)⁻¹ • input 3) = flux := by
  unfold radialCovariantKernel
  rw [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply, radialSevenSlotKernel_action]
  exact radialNormalizedCovariantKernel_correctedFlux_eq parameters L compact state r small
    angular cell _ flux fluxSupported fluxDerivative
    (radialNormalizedSevenInput_derivative parameters r angular cell input scalarDerivative)

end Grad.AnnularReconstruction
