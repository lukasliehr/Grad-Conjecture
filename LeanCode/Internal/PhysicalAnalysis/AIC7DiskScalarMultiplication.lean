import AIC6CutoffTestCalculus
import GC18APScalarJet

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace Grad.InteriorLocalization
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.CircularHighWeak

/-- Multiplication on the original ordinary-area disk L2 space, using the
accepted matrix-multiplier construction. -/
def diskScalar (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar) :
    DiskL2 1 →L[ℂ] DiskL2 1 :=
  closedOperatorL2 (apScalarOperatorJet 1 scalar smooth).value

theorem diskScalar_ae (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (field : DiskL2 1) :
    ∀ᵐ point ∂volume.restrict openUnitDisk,
      diskScalar scalar smooth field point = scalar point • field point := by
  filter_upwards [closedOperatorL2_ae (apScalarOperatorJet 1 scalar smooth).value field,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point action inside
  rw [diskScalar, action]
  simp only [closedDiskLift, openDiskMembershipClosed point inside, dite_true]
  rfl

theorem diskScalar_bound (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (field : DiskL2 1) :
    ‖diskScalar scalar smooth field‖ ≤ ‖(apScalarOperatorJet 1 scalar smooth).value‖ * ‖field‖ :=
  closedOperatorL2_apply_norm_le _ field

theorem diskScalar_pairing (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (field : DiskL2 1) (vector : PhysicalValue 1) (test : Spatial → ℝ) :
    (∫ point in openUnitDisk, test point • inner ℂ vector (diskScalar scalar smooth field point)) =
      ∫ point in openUnitDisk, (scalar point * test point) • inner ℂ vector (field point) := by
  apply integral_congr_ae
  filter_upwards [diskScalar_ae scalar smooth field] with point multiplication
  rw [multiplication, RCLike.real_smul_eq_coe_smul (K := ℂ) (scalar point) (field point),
    inner_smul_right]
  change (test point : ℂ) * ((scalar point : ℂ) * _) =
    ((scalar point * test point : ℝ) : ℂ) * _
  push_cast
  ring

/-- The literal L2 right side of the cutoff Laplacian. Every first derivative
is a coordinate of the same completed disk H1 field. -/
def localizedDiskLaplacian (field : diskGrade) (laplacian : DiskL2 1) : DiskL2 1 :=
  diskScalar interiorCutoff.toFun interiorCutoff.smooth laplacian +
    (2 : ℂ) • diskScalar (firstTestDerivative 0 interiorCutoff.toFun)
      (firstTestDerivative_smooth 0 _ interiorCutoff.smooth) (diskGradX field) +
    (2 : ℂ) • diskScalar (firstTestDerivative 1 interiorCutoff.toFun)
      (firstTestDerivative_smooth 1 _ interiorCutoff.smooth) (diskGradY field) +
    diskScalar (secondTestDerivative 0 interiorCutoff.toFun)
      (secondTestDerivative_smooth 0 _ interiorCutoff.smooth) (diskBulk field) +
    diskScalar (secondTestDerivative 1 interiorCutoff.toFun)
      (secondTestDerivative_smooth 1 _ interiorCutoff.smooth) (diskBulk field)

end Grad.InteriorLocalization
