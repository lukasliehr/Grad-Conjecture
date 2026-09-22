import AKBL3SameFixedCurlGauge
import AKBC7OriginalGaugeTailRecovery
import AHS5ActualCovariantGaugeConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.OriginalKernelCovariantRecovery
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

/-- The actual normalized seven-row native covariant satisfies both original
physical gauge means. This is before Cartesian H1 and keeps the scalar row's
native zero angular mode as the only support condition. -/
theorem startupNative_normalizedCovariant_gauged (parameters : PhaseParameters)
    (length compact : ℝ) (state : RadialCoefficientState parameters length compact)
    (radius : RadialPoint)
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
      radialMassLowRadius parameters length compact) (angular cell : ℕ)
    (input : SevenSlotTrace (radialKernelParameters parameters radius) angular cell)
    (supported : IsAngularMeanFree (radialKernelParameters parameters radius) angular cell (input 3)) :
    radialPhysicalGaugeMeans parameters length compact state radius angular cell
      (fullNegativeKernelAction (radialKernelParameters parameters radius) angular cell
        (radialNormalizedCovariantKernel parameters length compact state radius small)
        (sevenSlotFlatten (radialKernelParameters parameters radius) angular cell input)) = 0 := by
  unfold radialNormalizedCovariantKernel
  rw [fullNegativeKernelAction_add, radialPhysicalGaugeMeans_add,
    fullNegativeKernelAction_comp, ContinuousLinearMap.comp_apply,
    radialUnknownUKernel_gauged, zero_add]
  exact radialKnownAStarKernel_gauged parameters length compact state radius
    (small.trans (min_le_left _ _)) angular cell input supported

/-- The existing original Gamma inverse recovers this SAME actual native
covariant from its literal fixed quotient, without a smooth-core premise. -/
theorem startupNative_normalizedCovariant_current_recovers (parameters : PhaseParameters)
    (length compact : ℝ) (state : RadialCoefficientState parameters length compact)
    (radius : RadialPoint)
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
      radialMassLowRadius parameters length compact)
    (gaugeSmall : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
      radialGaugeLowRadius parameters length compact) (angular cell : ℕ)
    (input : SevenSlotTrace (radialKernelParameters parameters radius) angular cell)
    (supported : IsAngularMeanFree (radialKernelParameters parameters radius) angular cell (input 3)) :
    fullNegativeKernelAction (radialKernelParameters parameters radius) angular cell
      (radialGaugeQKernel parameters length compact state radius gaugeSmall)
      (originalCovariantUngauged (radialKernelParameters parameters radius) angular cell
        (fullNegativeKernelAction (radialKernelParameters parameters radius) angular cell
          (radialNormalizedCovariantKernel parameters length compact state radius small)
          (sevenSlotFlatten (radialKernelParameters parameters radius) angular cell input))) =
      fullNegativeKernelAction (radialKernelParameters parameters radius) angular cell
        (radialNormalizedCovariantKernel parameters length compact state radius small)
        (sevenSlotFlatten (radialKernelParameters parameters radius) angular cell input) :=
  originalCovariantGauge_recovers parameters angular cell length compact state radius gaugeSmall _
    (startupNative_normalizedCovariant_gauged parameters length compact state radius small angular cell input supported)

end Grad.CartesianStartup
