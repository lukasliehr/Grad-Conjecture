import ANG11FiniteModeConsumer

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open Set
open scoped ContDiff
namespace Grad.CircularHighWeak
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange
open Grad.PhysicalFamily Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Physical.RadialLedger

/-- The literal Cartesian vector field R=x∂y−y∂x on the actual H1 completion. -/
def diskRotation : diskGrade →L[ℂ] DiskL2 1 :=
  (diskCoordinateAction 1 0).comp diskGradY - (diskCoordinateAction 1 1).comp diskGradX

theorem diskGradX_partial_core (field : ClosedJet 1) :
    diskGradX (diskCoreInto field) = closedL2Core (partialJet 0 field) := by
  exact (diskGradX_core field).trans (congrArg closedContinuousToDiskL2 (partialJet_zero_value field).symm)

theorem diskGradY_partial_core (field : ClosedJet 1) :
    diskGradY (diskCoreInto field) = closedL2Core (partialJet 1 field) := by
  exact (diskGradY_core field).trans (congrArg closedContinuousToDiskL2 (partialJet_one_value field).symm)

theorem diskRotation_core (field : ClosedJet 1) :
    diskRotation (diskCoreInto field) = closedL2Core (rotationJet field) := by
  change diskCoordinateAction 1 0 (diskGradY (diskCoreInto field)) -
    diskCoordinateAction 1 1 (diskGradX (diskCoreInto field)) = _
  have first := (congrArg (diskCoordinateAction 1 0) (diskGradY_partial_core field)).trans
    (diskCoordinateAction_core 0 (partialJet 1 field))
  have second := (congrArg (diskCoordinateAction 1 1) (diskGradX_partial_core field)).trans
    (diskCoordinateAction_core 1 (partialJet 0 field))
  exact (congrArg₂ (fun first second : DiskL2 1 => first - second) first second).trans
    (closedL2Core.map_sub _ _).symm

theorem diskRotation_gradient_bound (field : diskGrade) :
    ‖diskRotation field‖ ^ 2 ≤ ‖diskGradX field‖ ^ 2 + ‖diskGradY field‖ ^ 2 := by
  apply isClosed_property diskCoreInto_denseRange
    (isClosed_le (diskRotation.continuous.norm.pow 2)
      ((diskGradX.continuous.norm.pow 2).add (diskGradY.continuous.norm.pow 2))) _ field
  intro core
  have bound := rotationJet_L2_bound core
  change ‖closedL2Core (rotationJet core)‖ ^ 2 ≤
    ‖closedL2Core (partialJet 0 core)‖ ^ 2 + ‖closedL2Core (partialJet 1 core)‖ ^ 2 at bound
  exact (congrArg (fun value : DiskL2 1 => ‖value‖ ^ 2) (diskRotation_core core)).le.trans
    (bound.trans_eq (congrArg₂ (fun first second : DiskL2 1 => ‖first‖ ^ 2 + ‖second‖ ^ 2)
      (diskGradX_partial_core core).symm (diskGradY_partial_core core).symm))

theorem diskRotation_contract (field : diskGrade) : ‖diskRotation field‖ ≤ ‖field‖ := by
  have gradient := diskRotation_gradient_bound field
  have norm := diskGrade_norm_sq field
  nlinarith [norm_nonneg field, norm_nonneg (diskRotation field), sq_nonneg ‖diskBulk field‖]

/-- Distributional identification uses every actual compact Cartesian test. -/
theorem diskRotation_weak (field : diskGrade) (cell : ℤ) (vector : Grad.GenericCarriers.PhysicalValue 1)
    (test : Grad.PDEBootstrap.Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (supported : tsupport test ⊆ openUnitDisk) :
    apDiskPairing 1 cell vector test smooth compact (diskRotation field) =
      angularWeakPairing 1 cell vector test smooth compact (diskBulk field) := by
  apply isClosed_property diskCoreInto_denseRange
    (isClosed_eq ((apDiskPairing 1 cell vector test smooth compact).continuous.comp diskRotation.continuous)
      ((angularWeakPairing 1 cell vector test smooth compact).continuous.comp diskBulk.continuous)) _ field
  intro core
  exact (congrArg (apDiskPairing 1 cell vector test smooth compact) (diskRotation_core core)).trans
    ((rotationJet_weak core cell vector test smooth compact supported).trans
      (congrArg (angularWeakPairing 1 cell vector test smooth compact) (diskBulk_core core).symm))

def highRotation : highDiskGrade →L[ℂ] DiskL2 1 := diskRotation.comp highDiskGrade.subtypeL

theorem highRotation_contract (field : highDiskGrade) : ‖highRotation field‖ ≤ ‖field‖ :=
  diskRotation_contract field.val

theorem highRotation_gradient_bound (field : highDiskGrade) :
    ‖highRotation field‖ ^ 2 ≤ ‖highGradX field‖ ^ 2 + ‖highGradY field‖ ^ 2 :=
  diskRotation_gradient_bound field.val

end Grad.CircularHighWeak
