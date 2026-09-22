import AKBC7OriginalGaugeTailRecovery

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (r : RadialPoint) (angular cell : ℕ)
private abbrev rp := radialKernelParameters parameters r

theorem originalCovariantFreeChart_eq (rotated : NegativeTrace (rp parameters r) angular cell 3)
    (input : SevenSlotTrace (rp parameters r) angular cell) :
    originalCovariantFreeChart (rp parameters r) angular cell rotated (input 3)=
      radialSevenFreeChart parameters r angular cell
        (forceCoordinateTrace (rp parameters r) angular cell 0 rotated) input := by
  simp only [originalCovariantFreeChart,originalTraceVector,radialSevenFreeChart,
    actualUnknownQAKernel,fullNegativeKernelAction_comp,ContinuousLinearMap.comp_apply,map_zero,add_zero]

variable (L compact : ℝ) (state : RadialCoefficientState parameters L compact)
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7≤
  radialGaugeLowRadius parameters L compact)

theorem originalCovariant_actualChart (field rotated twice : NegativeTrace (rp parameters r) angular cell 3)
    (input : SevenSlotTrace (rp parameters r) angular cell)
    (scalarTwice : NegativeTrace (rp parameters r) angular cell 1)
    (rotation : IsAngularDerivative (rp parameters r) angular cell field rotated)
    (second : IsAngularDerivative (rp parameters r) angular cell rotated twice)
    (scalarRotation : IsAngularDerivative (rp parameters r) angular cell (input 3) (input 1))
    (scalarSecond : IsAngularDerivative (rp parameters r) angular cell (input 1) scalarTwice)
    (scalarMean : IsAngularMeanFree (rp parameters r) angular cell (input 3))
    (gauged : radialPhysicalGaugeMeans parameters L compact state r angular cell field=0) :
    radialForceChart parameters L compact state r small angular cell
      (originalCovariantEncoded (rp parameters r) angular cell field rotated twice scalarTwice)
      (radialSevenFreeChart parameters r angular cell
        (forceCoordinateTrace (rp parameters r) angular cell 0 rotated) input)=field := by
  rw [radialForceChart,← originalCovariantFreeChart_eq,
    originalCovariantEncoded_decodes (rp parameters r) angular cell field rotated twice
      (input 3) (input 1) scalarTwice rotation second scalarRotation scalarSecond scalarMean]
  exact originalCovariantGauge_recovers parameters angular cell L compact state r small field gauged

include small in
theorem originalCovariant_actualRotation (field rotated twice : NegativeTrace (rp parameters r) angular cell 3)
    (input : SevenSlotTrace (rp parameters r) angular cell)
    (scalarTwice : NegativeTrace (rp parameters r) angular cell 1)
    (rotation : IsAngularDerivative (rp parameters r) angular cell field rotated)
    (second : IsAngularDerivative (rp parameters r) angular cell rotated twice)
    (scalarRotation : IsAngularDerivative (rp parameters r) angular cell (input 3) (input 1))
    (scalarSecond : IsAngularDerivative (rp parameters r) angular cell (input 1) scalarTwice)
    (scalarMean : IsAngularMeanFree (rp parameters r) angular cell (input 3))
    (gauged : radialPhysicalGaugeMeans parameters L compact state r angular cell field=0) :
    radialForceChartRotation parameters r angular cell
      (originalCovariantEncoded (rp parameters r) angular cell field rotated twice scalarTwice)
      (radialSevenFreeChartRotation parameters r angular cell
        (forceCoordinateTrace (rp parameters r) angular cell 0 rotated) input)=rotated := by
  have derivative := radialForceChart_derivative parameters L compact state r small angular cell
    (originalCovariantEncoded (rp parameters r) angular cell field rotated twice scalarTwice)
    _ _ (radialSevenFreeChart_derivative parameters r angular cell
      (forceCoordinateTrace (rp parameters r) angular cell 0 rotated) input
      (rotation.constantMatrix (matrixUnit 0 (0 : Fin 3))).meanFree scalarRotation)
  rw [originalCovariant_actualChart parameters r angular cell L compact state small field rotated twice input
    scalarTwice rotation second scalarRotation scalarSecond scalarMean gauged] at derivative
  apply NegativeTrace.ext_coefficient (rp parameters r) angular cell
  intro mode
  exact (derivative mode).trans (rotation mode).symm

end Grad.OriginalKernelCovariantRecovery
