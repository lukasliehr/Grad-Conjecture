import ABG1OrdinaryAngularModes
import AIP9PeriodizationCutoff

noncomputable section
set_option maxHeartbeats 800000
open scoped ContDiff
namespace Grad.OrdinaryDiskMultiplier
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Radial Grad.OrdinaryDiskCalculus
open Grad.InteriorLocalization Grad.InteriorPeriodization Grad.PDEBootstrap Grad.CompactCutoff
attribute [local instance] unitNormedSpace

/-- The scalar is invariant along the actual closed-disk rotation orbit. -/
def RadialScalar (scalar : Spatial → ℝ) : Prop :=
  ∀ angle point, scalar (rotatedPoint angle point).val = scalar point.val

theorem scalarJet_value (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (core : ClosedJet 1) (point : ClosedDisk) :
    (apProductJet (apScalarOperatorJet 1 scalar smooth) core).value point = scalar point.val • core.value point := by
  rw [apProductJet_value]
  rfl

theorem angularScalarJet_commute (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (radial : RadialScalar scalar) (mode : ℤ) (core : ClosedJet 1) :
    angularClosedJet mode (apProductJet (apScalarOperatorJet 1 scalar smooth) core) =
      apProductJet (apScalarOperatorJet 1 scalar smooth) (angularClosedJet mode core) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [angularClosedJet_value, scalarJet_value, angularClosedJet_value]
  have integrand (angle : ℝ) : angularCharacter mode angle •
      (apProductJet (apScalarOperatorJet 1 scalar smooth) core).value (rotatedPoint angle point) =
      scalar point.val • (angularCharacter mode angle • core.value (rotatedPoint angle point)) := by
    rw [scalarJet_value, radial]
    exact smul_comm _ _ _
  simp_rw [integrand]
  rw [intervalIntegral.integral_smul]
  exact smul_comm _ _ _

theorem unitMode_scalar (grade : ℕ) (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (radial : RadialScalar scalar) (mode : ℤ) (field : unitDiskSobolev grade) :
    unitScalar grade scalar smooth (unitMode grade mode field) =
      unitMode grade mode (unitScalar grade scalar smooth field) := by
  apply isClosed_property (unitDiskCoreInto_denseRange grade)
    (isClosed_eq ((unitScalar grade scalar smooth).continuous.comp (unitMode grade mode).continuous)
      ((unitMode grade mode).continuous.comp (unitScalar grade scalar smooth).continuous)) _ field
  intro core
  exact (congrArg (unitScalar grade scalar smooth) (unitMode_core grade mode core)).trans
    ((unitProduct_core grade _ (angularClosedJet mode core)).trans
      ((congrArg (unitDiskCoreInto grade) (angularScalarJet_commute scalar smooth radial mode core).symm).trans
        ((unitMode_core grade mode _).symm.trans
          (congrArg (unitMode grade mode) (unitProduct_core grade _ core).symm))))

theorem diskMode_scalar (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (radial : RadialScalar scalar) (mode : ℤ) (field : DiskL2 1) :
    diskScalar scalar smooth (diskMode mode field) = diskMode mode (diskScalar scalar smooth field) := by
  apply isClosed_property closedL2Core_denseRange
    (isClosed_eq ((diskScalar scalar smooth).continuous.comp (diskMode mode).continuous)
      ((diskMode mode).continuous.comp (diskScalar scalar smooth).continuous)) _ field
  intro core
  exact (congrArg (diskScalar scalar smooth) (diskMode_core mode core)).trans
    ((productCore_L2 _ (angularClosedJet mode core)).symm.trans
      ((congrArg closedL2Core (angularScalarJet_commute scalar smooth radial mode core).symm).trans
        ((diskMode_core mode _).symm.trans
          (congrArg (diskMode mode) (productCore_L2 _ core)))))

end Grad.OrdinaryDiskMultiplier
