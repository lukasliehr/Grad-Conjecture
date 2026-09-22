import AKBC8SameActualForceChart

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
  radialFirstLowRadius parameters L compact) (angular cell : ℕ)
private abbrev rp := radialKernelParameters parameters r

/-- The original covariant, under its literal normalized force rows and
physical gauges, equals the immutable pre-mass reconstruction. -/
theorem originalCovariant_preMass (field rotated twice : NegativeTrace (rp parameters r) angular cell 3)
    (input : SevenSlotTrace (rp parameters r) angular cell)
    (scalarTwice : NegativeTrace (rp parameters r) angular cell 1)
    (rotation : IsAngularDerivative (rp parameters r) angular cell field rotated)
    (second : IsAngularDerivative (rp parameters r) angular cell rotated twice)
    (scalarRotation : IsAngularDerivative (rp parameters r) angular cell (input 3) (input 1))
    (scalarSecond : IsAngularDerivative (rp parameters r) angular cell (input 1) scalarTwice)
    (scalarMean : IsAngularMeanFree (rp parameters r) angular cell (input 3))
    (sourceRotation : IsAngularDerivative (rp parameters r) angular cell (input 4) (input 5))
    (gauged : radialPhysicalGaugeMeans parameters L compact state r angular cell field=0)
    (first : -forceCoordinateTrace (rp parameters r) angular cell 1 rotated -
      (2 : ℂ) • forceCoordinateTrace (rp parameters r) angular cell 0 field +
      fullNegativeKernelAction (rp parameters r) angular cell (radialForceKernel parameters L compact state r 0 0) field +
      input 1=input 4)
    (third : forceCoordinateTrace (rp parameters r) angular cell 2 rotated +
      forceMeanFreeTrace (rp parameters r) angular cell
        (fullNegativeKernelAction (rp parameters r) angular cell (radialForceKernel parameters L compact state r 1 0) field) -
      (L : ℂ)⁻¹ • input 2=input 6) :
    field=radialPreMassCovariantTrace parameters L compact state r small angular cell
      (forceCoordinateTrace (rp parameters r) angular cell 0 rotated) input := by
  let mass := forceCoordinateTrace (rp parameters r) angular cell 0 rotated
  let encoded := originalCovariantEncoded (rp parameters r) angular cell field rotated twice scalarTwice
  let known := radialSevenFreeChart parameters r angular cell mass input
  let knownDerivative := radialSevenFreeChartRotation parameters r angular cell mass input
  have massMean : IsAngularMeanFree (rp parameters r) angular cell mass :=
    (rotation.constantMatrix (matrixUnit 0 (0 : Fin 3))).meanFree
  have supported : EncodedSupport (rp parameters r) angular cell encoded :=
    originalCovariantEncoded_support (rp parameters r) angular cell field rotated twice
      (input 1) scalarTwice rotation second scalarSecond
  have chart : radialForceChart parameters L compact state r (small.trans (min_le_left _ _)) angular cell encoded known=field :=
    originalCovariant_actualChart parameters r angular cell L compact state (small.trans (min_le_left _ _)) field rotated twice input
      scalarTwice rotation second scalarRotation scalarSecond scalarMean gauged
  have rotatedChart : radialForceChartRotation parameters r angular cell encoded knownDerivative=rotated :=
    originalCovariant_actualRotation parameters r angular cell L compact state (small.trans (min_le_left _ _)) field rotated twice input
      scalarTwice rotation second scalarRotation scalarSecond scalarMean gauged
  have forces : radialFirstForceTrace parameters L compact state r (small.trans (min_le_left _ _)) angular cell encoded known=input 4 ∧
      radialThirdForceTrace parameters L compact state r (small.trans (min_le_left _ _)) angular cell encoded known (input 2)=input 6 := by
    constructor
    · calc
        _ = -forceCoordinateTrace (rp parameters r) angular cell 1
              (radialForceChartRotation parameters r angular cell encoded knownDerivative) -
            (2 : ℂ) • forceCoordinateTrace (rp parameters r) angular cell 0
              (radialForceChart parameters L compact state r (small.trans (min_le_left _ _)) angular cell encoded known) +
            fullNegativeKernelAction (rp parameters r) angular cell (radialForceKernel parameters L compact state r 0 0)
              (radialForceChart parameters L compact state r (small.trans (min_le_left _ _)) angular cell encoded known) +input 1 := by
          unfold radialFirstForceTrace radialForceChartRotation
          rw [map_add,(radialSevenFreeChartRotation_tail parameters r angular cell mass input).1]
          abel
        _ = input 4 := by rw [chart,rotatedChart]; exact first
    · calc
        _ = forceCoordinateTrace (rp parameters r) angular cell 2
              (radialForceChartRotation parameters r angular cell encoded knownDerivative) +
            forceMeanFreeTrace (rp parameters r) angular cell
              (fullNegativeKernelAction (rp parameters r) angular cell (radialForceKernel parameters L compact state r 1 0)
                (radialForceChart parameters L compact state r (small.trans (min_le_left _ _)) angular cell encoded known)) -
            (L : ℂ)⁻¹ • input 2 := by
          unfold radialThirdForceTrace radialForceChartRotation
          rw [map_add,(radialSevenFreeChartRotation_tail parameters r angular cell mass input).2,add_zero,
            encodedRotation_third,angularMeanFreeKernel_action_eq _ _ _ _
              (forceCoordinate_meanFree (rp parameters r) angular cell encoded 2 supported.2.2)]
        _ = input 6 := by rw [chart,rotatedChart]; exact third
  have unique := radialEncodedFirstInverse_force_unique parameters L compact state r small angular cell
    encoded known knownDerivative (input 2) (input 4) (input 5) (input 6) supported
    (radialSevenFreeChart_first_meanFree parameters r angular cell mass input)
    (radialSevenFreeChart_derivative parameters r angular cell mass input massMean scalarRotation)
    sourceRotation forces
  rw [← radialSevenEncodedTrace_eq_inverse parameters L compact state r small angular cell mass input massMean] at unique
  rw [← chart,unique,radialSevenEncodedTrace_same_covariant]
  rfl

end Grad.OriginalKernelCovariantRecovery
