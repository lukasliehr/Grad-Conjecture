import AHP21RadialPhysicalFluxPrimitives

noncomputable section
set_option maxHeartbeats 1800000

namespace Grad.AnnularReconstruction
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
private abbrev rp := radialKernelParameters parameters r

/-- Literal AF3 signed mean-free flux. The scalar argument is xi/r; sigma
and kappa1 are the accepted original physical coefficient families at r. -/
def radialCorrectedFluxTrace (angular cell : ℕ)
    (covariant : NegativeTrace (rp parameters r) angular cell 3)
    (normalizedScalar : NegativeTrace (rp parameters r) angular cell 1) :
    NegativeTrace (rp parameters r) angular cell 1 :=
  fullNegativeKernelAction (rp parameters r) angular cell (angularMeanFreeKernel (rp parameters r) 1)
    (-fullNegativeKernelAction (rp parameters r) angular cell
      (coordinateProjectionKernel (rp parameters r) 3 0) covariant +
      fullNegativeKernelAction (rp parameters r) angular cell
        (radialSigmaKernel parameters L compact state r 0) covariant +
      fullNegativeKernelAction (rp parameters r) angular cell
        (radialSigmaComponentKernel parameters L compact state r 1) normalizedScalar)

theorem radialCorrectedFluxTrace_meanFree (angular cell : ℕ)
    (covariant : NegativeTrace (rp parameters r) angular cell 3)
    (normalizedScalar : NegativeTrace (rp parameters r) angular cell 1) :
    IsAngularMeanFree (rp parameters r) angular cell
      (radialCorrectedFluxTrace parameters L compact state r angular cell covariant normalizedScalar) :=
  angularMeanFreeKernel_action_meanFree (rp parameters r) angular cell _

theorem radialCorrectedFluxTrace_derivative (angular cell : ℕ)
    (covariant rotated : NegativeTrace (rp parameters r) angular cell 3)
    (scalar scalarRotation : NegativeTrace (rp parameters r) angular cell 1)
    (covariantDerivative : IsAngularDerivative (rp parameters r) angular cell covariant rotated)
    (scalarDerivative : IsAngularDerivative (rp parameters r) angular cell scalar scalarRotation) :
    IsAngularDerivative (rp parameters r) angular cell
      (radialCorrectedFluxTrace parameters L compact state r angular cell covariant scalar)
      (fullNegativeKernelAction (rp parameters r) angular cell (angularMeanFreeKernel (rp parameters r) 1)
        (-fullNegativeKernelAction (rp parameters r) angular cell
          (coordinateProjectionKernel (rp parameters r) 3 0) rotated +
          (fullNegativeKernelAction (rp parameters r) angular cell
            (radialRotatedSigmaKernel parameters L compact state r 0) covariant +
           fullNegativeKernelAction (rp parameters r) angular cell
            (radialSigmaKernel parameters L compact state r 0) rotated) +
          (fullNegativeKernelAction (rp parameters r) angular cell
            (radialRotatedSigmaComponentKernel parameters L compact state r 1) scalar +
           fullNegativeKernelAction (rp parameters r) angular cell
            (radialSigmaComponentKernel parameters L compact state r 1) scalarRotation))) := by
  have first := covariantDerivative.constantMatrix
    (Grad.GaugeCoefficients.Physical.Ledger.matrixUnit (0 : Fin 1) (0 : Fin 3))
  have sigma := radialSigmaKernel_derivative parameters L compact state r angular cell
    covariant rotated covariantDerivative
  have kappa := radialSigmaComponentKernel_derivative parameters L compact state r 1 angular cell
    scalar scalarRotation scalarDerivative
  exact ((first.neg.add sigma).add kappa).scalarMode angularMeanFreeMultiplier 1
    angularMeanFreeMultiplier_norm_le

variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialFirstLowRadius parameters L compact)

def radialPreMassCovariantTrace (angular cell : ℕ)
    (mass : NegativeTrace (rp parameters r) angular cell 1)
    (input : SevenSlotTrace (rp parameters r) angular cell) :
    NegativeTrace (rp parameters r) angular cell 3 :=
  fullNegativeKernelAction (rp parameters r) angular cell
    (radialUnknownUKernel parameters L compact state r small) mass +
  fullNegativeKernelAction (rp parameters r) angular cell
    (radialKnownAStarKernel parameters L compact state r small)
    (sevenSlotFlatten (rp parameters r) angular cell input)

/-- AF11–12 at the actual radius, with the signed -A term and all four
inhomogeneous products. It follows from genuine coefficient product rules. -/
theorem radialPreMassCorrectedFlux_derivative (angular cell : ℕ)
    (mass : NegativeTrace (rp parameters r) angular cell 1)
    (input : SevenSlotTrace (rp parameters r) angular cell)
    (massSupported : IsAngularMeanFree (rp parameters r) angular cell mass)
    (scalarDerivative : IsAngularDerivative (rp parameters r) angular cell (input 3) (input 1)) :
    IsAngularDerivative (rp parameters r) angular cell
      (radialCorrectedFluxTrace parameters L compact state r angular cell
        (radialPreMassCovariantTrace parameters L compact state r small angular cell mass input) (input 3))
      (fullNegativeKernelAction (rp parameters r) angular cell
        (radialMassPerturbationKernel parameters L compact state r small) mass - mass +
       fullNegativeKernelAction (rp parameters r) angular cell
        (radialKnownJStarKernel parameters L compact state r small)
        (sevenSlotFlatten (rp parameters r) angular cell input)) := by
  have unknown := radialUnknownUKernel_derivative parameters L compact state r small angular cell mass massSupported
  have known := radialKnownAStarKernel_derivative parameters L compact state r small angular cell input scalarDerivative
  have flux := radialCorrectedFluxTrace_derivative parameters L compact state r angular cell
    _ _ (input 3) (input 1) (unknown.add known) scalarDerivative
  change IsAngularDerivative (rp parameters r) angular cell
    (radialCorrectedFluxTrace parameters L compact state r angular cell
      (radialPreMassCovariantTrace parameters L compact state r small angular cell mass input) (input 3)) _ at flux
  simp only [map_add, radialUnknownVKernel_first, radialKnownRAStarKernel_first, add_zero] at flux
  convert flux using 1
  unfold radialMassPerturbationKernel radialKnownJStarKernel
  simp only [fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    fullNegativeKernelAction_add, sevenInputSlotKernel_action, map_add, map_neg,
    angularMeanFreeKernel_action_eq (rp parameters r) angular cell mass massSupported]
  abel

end Grad.AnnularReconstruction
