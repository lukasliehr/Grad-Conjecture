import AIP8CompactDiskIntegral
import AIC14ActualInteriorConsumer

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology

namespace Grad.InteriorPeriodization
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.DiskExtension.Operator Grad.FourierGrade Grad.COR12Extension
open Grad.InteriorLocalization Grad.CompactCutoff

/-- A larger cutoff, equal to one on a neighborhood of the localized PDE's
support and vanishing before the reflected Seeley extension can contribute. -/
def periodizationCutoff := diskCutoff (2 / 3 : ℝ) (1 / 24 : ℝ) (by norm_num) (by norm_num)

theorem periodizationCutoff_support : tsupport periodizationCutoff.toFun =
    Metric.closedBall (0 : SpatialPlane) (3 / 4) := by
  simpa only [periodizationCutoff, show (2 / 3 : ℝ) + 2 * (1 / 24) = 3 / 4 by norm_num] using
    diskCutoff_support (2 / 3 : ℝ) (1 / 24 : ℝ) (by norm_num) (by norm_num)

theorem periodizationCutoff_one : Set.EqOn periodizationCutoff.toFun (fun _ => 1)
    (Metric.closedBall (0 : SpatialPlane) (17 / 24)) := by
  simpa only [periodizationCutoff, show (2 / 3 : ℝ) + 1 / 24 = 17 / 24 by norm_num] using
    diskCutoff_one (2 / 3 : ℝ) (1 / 24 : ℝ) (by norm_num) (by norm_num)

def periodizationCore (field : ClosedJet 1) : ClosedJet 1 :=
  globalClosedJet (fun point => periodizationCutoff.toFun point • smoothClosedExtension field point)
    (periodizationCutoff.smooth.smul (smoothClosedExtension_smooth field))

theorem periodizationCore_value (field : ClosedJet 1) (point : ClosedDisk) :
    (periodizationCore field).value point = periodizationCutoff.toFun point.val • field.value point := by
  rw [periodizationCore, globalClosedJet_value, smoothClosedExtension_value]

theorem periodizationCore_supported (field : ClosedJet 1) :
    ∀ point : ClosedDisk, (3 / 4 : ℝ) < ‖point.val‖ → (periodizationCore field).value point = 0 := by
  intro point outside
  rw [periodizationCore_value]
  have absent : point.val ∉ tsupport periodizationCutoff.toFun := by
    rw [periodizationCutoff_support]
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using outside
  rw [image_eq_zero_of_notMem_tsupport absent, zero_smul]

theorem periodizationCore_L2 (field : ClosedJet 1) :
    closedL2Core (periodizationCore field) =
      diskScalar periodizationCutoff.toFun periodizationCutoff.smooth (closedL2Core field) := by
  apply Lp.ext
  filter_upwards [closedContinuousToDiskL2_ae (periodizationCore field).value,
    closedContinuousToDiskL2_ae field.value,
    diskScalar_ae periodizationCutoff.toFun periodizationCutoff.smooth (closedL2Core field),
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point first second multiplication inside
  change closedContinuousToDiskL2 (periodizationCore field).value point = _
  rw [first, multiplication]
  change closedDiskLift (periodizationCore field).value point =
    periodizationCutoff.toFun point • closedContinuousToDiskL2 field.value point
  rw [second, closedDiskLift, dif_pos (openDiskMembershipClosed point inside),
    closedDiskLift, dif_pos (openDiskMembershipClosed point inside), periodizationCore_value]

end Grad.InteriorPeriodization
