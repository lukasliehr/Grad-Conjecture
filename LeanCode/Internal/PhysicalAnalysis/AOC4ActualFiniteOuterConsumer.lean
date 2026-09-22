import AOC3LiteralBulkIdentity

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace Grad.ActualOuterCollar
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.ActualInverseInduction Grad.InteriorLocalization
open Grad.AnnularSourceGraph Grad.BoundaryLift

def finiteHighModes (modes : Finset ℤ) : Finset ℤ := modes.filter (fun mode => mode ∉ lowAngularModes)

private theorem selectedModes_remove_zero (modes : Finset ℤ) (field : DiskL2 1)
    (vanish : ∀ mode ∈ lowAngularModes, diskMode mode field = 0) :
    diskSelectedModes (finiteHighModes modes) field = diskSelectedModes modes field := by
  rw [diskSelectedModes_apply, diskSelectedModes_apply]
  unfold finiteHighModes
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro mode _
  by_cases high : mode ∉ lowAngularModes
  · rw [if_pos high]
  · rw [if_neg high]
    exact (vanish mode (not_not.mp high)).symm

theorem diskSelectedModes_remove_low (modes : Finset ℤ) (field : highDiskGrade) :
    diskSelectedModes (finiteHighModes modes) (highDiskBulk field) =
      diskSelectedModes modes (highDiskBulk field) :=
  selectedModes_remove_zero modes (highDiskBulk field) (highDiskBulk_spectral field)

/-- The literal finite angular outer field. The only omitted terms are the
five coefficients already zero for the constructed high inverse. -/
def finiteOuterField (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2)
    (point : SpatialPlane) : ComplexEuclidean 1 :=
  ∑ mode ∈ finiteHighModes modes,
    outerRadialField mode
      (radialSectionExtension 1 (1 / 2) (by norm_num)
        (diskRadialValueSection (1 / 2) (by norm_num) (by norm_num) mode
          (highRobinWeakInverse parameter source).val)) point

theorem finiteOuterField_smooth (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2)
    (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    ContDiffOn ℝ ∞ (finiteOuterField modes parameter source) closedUnitDisk := by
  apply ContDiffOn.sum
  intro mode member
  apply outerRadialField_smooth
  exact weakInverse_closedCollar_smooth (1 / 2) (by norm_num) (by norm_num)
    mode (Finset.mem_filter.mp member).2 parameter source core same

theorem finiteOuterField_value (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2)
    (point : ClosedDisk) :
    actualOuterFiniteValue (finiteHighModes modes) (highRobinWeakInverse parameter source).val point =
      finiteOuterField modes parameter source point.val := by
  simp only [actualOuterFiniteValue, ContinuousMap.sum_apply]
  rfl

theorem finiteOuterField_bulk (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2) :
    closedContinuousToDiskL2
      (actualOuterFiniteValue (finiteHighModes modes) (highRobinWeakInverse parameter source).val) =
      diskScalar outerCutoffScalar outerCutoffScalar_smooth
        (highDiskBulk (highRobinWeakInverse parameter (highL2SelectedModes modes source))) := by
  exact (actualOuterFiniteValue_bulk (finiteHighModes modes) (highRobinWeakInverse parameter source).val).trans
    (congrArg (diskScalar outerCutoffScalar outerCutoffScalar_smooth)
      ((diskSelectedModes_remove_low modes (highRobinWeakInverse parameter source)).trans
        ((highSelectedModes_bulk modes (highRobinWeakInverse parameter source)).symm.trans
          (congrArg highDiskBulk (highRobinWeakInverse_selected parameter modes source)))))

private theorem continuousBulk_ae (value : C(ClosedDisk, ComplexEuclidean 1))
    (field : SpatialPlane → ComplexEuclidean 1) (target : DiskL2 1)
    (valueSame : ∀ point : ClosedDisk, value point = field point.val)
    (bulk : closedContinuousToDiskL2 value = target) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, field point = target point := by
  filter_upwards [closedContinuousToDiskL2_ae value,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point literal inside
  rw [bulk] at literal
  rw [literal]
  simp only [closedDiskLift, openDiskMembershipClosed point inside, dite_true]
  exact (valueSame ⟨point, openDiskMembershipClosed point inside⟩).symm

theorem finiteOuterField_bulk_ae (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, finiteOuterField modes parameter source point =
      diskScalar outerCutoffScalar outerCutoffScalar_smooth
        (highDiskBulk (highRobinWeakInverse parameter (highL2SelectedModes modes source))) point :=
  continuousBulk_ae _ _ _ (finiteOuterField_value modes parameter source)
    (finiteOuterField_bulk modes parameter source)

/-- Qualitative actual finite-angular outer reconstruction: the closed-disk
smooth function and the literal ordinary-area L2 identity refer to the same
ANH inverse of the selected original smooth source. No outer regularity or
radiality of the accepted cutoff is an input. -/
theorem actualFiniteOuterReconstruction (modes : Finset ℤ) (parameter : ℝ) (source : highDiskL2)
    (core : ClosedJet 1) (same : source.val = closedL2Core core) :
    ContDiffOn ℝ ∞ (finiteOuterField modes parameter source) closedUnitDisk ∧
    (∀ᵐ point ∂volume.restrict openUnitDisk, finiteOuterField modes parameter source point =
      diskScalar outerCutoffScalar outerCutoffScalar_smooth
        (highDiskBulk (highRobinWeakInverse parameter (highL2SelectedModes modes source))) point) :=
  ⟨finiteOuterField_smooth modes parameter source core same, finiteOuterField_bulk_ae modes parameter source⟩

end Grad.ActualOuterCollar
