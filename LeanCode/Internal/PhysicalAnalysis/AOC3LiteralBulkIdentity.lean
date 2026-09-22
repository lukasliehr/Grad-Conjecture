import AOC2ActualContinuousField

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace Grad.ActualOuterCollar
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.ActualInverseInduction Grad.InteriorLocalization
open Grad.AnnularSourceGraph Grad.BoundaryLift

theorem actualOuterModeValue_core_bulk (mode : ℤ) (core : ClosedJet 1) :
    closedContinuousToDiskL2 (actualOuterModeValue mode (diskCoreInto core)) =
      diskScalar outerCutoffScalar outerCutoffScalar_smooth (closedL2Core (angularClosedJet mode core)) := by
  apply Lp.ext
  filter_upwards [closedContinuousToDiskL2_ae (actualOuterModeValue mode (diskCoreInto core)),
    diskScalar_ae outerCutoffScalar outerCutoffScalar_smooth (closedL2Core (angularClosedJet mode core)),
    closedContinuousToDiskL2_ae (angularClosedJet mode core).value,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point leftAt rightAt coreAt inside
  change closedL2Core (angularClosedJet mode core) point = _ at coreAt
  rw [leftAt, rightAt, coreAt]
  simp only [closedDiskLift, openDiskMembershipClosed point inside, dite_true]
  exact actualOuterModeValue_core mode core ⟨point, openDiskMembershipClosed point inside⟩

/-- The continuous collar representative is literally the cutoff of the
same completed angular mode, for every original disk H1 field. -/
theorem actualOuterModeValue_bulk (mode : ℤ) (field : diskGrade) :
    closedContinuousToDiskL2 (actualOuterModeValue mode field) =
      diskScalar outerCutoffScalar outerCutoffScalar_smooth (diskMode mode (diskBulk field)) := by
  apply isClosed_property diskCoreInto_denseRange
    (isClosed_eq ((closedValueL2Continuous 1).continuous.comp (actualOuterModeValue_continuous mode))
      ((diskScalar outerCutoffScalar outerCutoffScalar_smooth).continuous.comp
        ((diskMode mode).continuous.comp diskBulk.continuous))) _ field
  intro core
  have angular : diskMode mode (diskBulk (diskCoreInto core)) = closedL2Core (angularClosedJet mode core) :=
    (congrArg (diskMode mode) (Grad.CircularHighWeak.diskBulk_core core)).trans (diskMode_core mode core)
  exact (actualOuterModeValue_core_bulk mode core).trans
    (congrArg (diskScalar outerCutoffScalar outerCutoffScalar_smooth) angular).symm

def actualOuterFiniteValue (modes : Finset ℤ) (field : diskGrade) : C(ClosedDisk, ComplexEuclidean 1) :=
  ∑ mode ∈ modes, actualOuterModeValue mode field

theorem actualOuterFiniteValue_bulk (modes : Finset ℤ) (field : diskGrade) :
    closedContinuousToDiskL2 (actualOuterFiniteValue modes field) =
      diskScalar outerCutoffScalar outerCutoffScalar_smooth (diskSelectedModes modes (diskBulk field)) := by
  change closedValueL2Continuous 1 (∑ mode ∈ modes, actualOuterModeValue mode field) = _
  rw [map_sum, diskSelectedModes_apply, map_sum]
  exact Finset.sum_congr rfl (fun mode _ => actualOuterModeValue_bulk mode field)

theorem highSelectedModes_bulk (modes : Finset ℤ) (field : highDiskGrade) :
    highDiskBulk (highSelectedModes modes field) = diskSelectedModes modes (highDiskBulk field) := by
  simp only [highSelectedModes, sum_apply, map_sum, highDiskMode_bulk, diskSelectedModes_apply]

/-- Exact finite angular inverse consumer. Selection commutes with the
already constructed ANH inverse; the Cartesian cutoff is applied afterward. -/
theorem finiteInverse_outer_bulk (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2) :
    closedContinuousToDiskL2 (actualOuterFiniteValue modes (highRobinWeakInverse parameter source).val) =
      diskScalar outerCutoffScalar outerCutoffScalar_smooth
        (highDiskBulk (highRobinWeakInverse parameter (highL2SelectedModes modes source))) := by
  exact (actualOuterFiniteValue_bulk modes (highRobinWeakInverse parameter source).val).trans
    (congrArg (diskScalar outerCutoffScalar outerCutoffScalar_smooth)
      ((highSelectedModes_bulk modes (highRobinWeakInverse parameter source)).symm.trans
        (congrArg highDiskBulk (highRobinWeakInverse_selected parameter modes source))))

end Grad.ActualOuterCollar
