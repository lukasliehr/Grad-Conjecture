import COR01Interface

noncomputable section

open Set
open scoped Topology

namespace Grad.ClosedJets

theorem openUnitDisk_eq_ball : openUnitDisk = Metric.ball 0 1 := by
  ext point
  change (‖point‖ < 1) ↔ dist point 0 < 1
  rw [dist_zero_right]

theorem closedUnitDisk_eq_closedBall : closedUnitDisk = Metric.closedBall 0 1 := by
  ext point
  change (‖point‖ ≤ 1) ↔ dist point 0 ≤ 1
  rw [dist_zero_right]

theorem openDisk_dense : DenseRange openDiskInclusion := by
  rw [show openDiskInclusion = Set.inclusion openDiskMembershipClosed from rfl,
    denseRange_inclusion_iff openDiskMembershipClosed]
  rw [openUnitDisk_eq_ball, closedUnitDisk_eq_closedBall, closure_ball 0 one_ne_zero]

theorem openDiskCell_dense : DenseRange openDiskCellInclusion := by
  have product := DenseRange.prodMap openDisk_dense (denseRange_id : DenseRange (id : CellCircle → CellCircle))
  change DenseRange (Prod.map openDiskInclusion (id : CellCircle → CellCircle))
  exact product

theorem continuousMap_eq_of_openDisk
    {Target : Type*} [TopologicalSpace Target] [T2Space Target]
    (first second : ContinuousMap ClosedDisk Target)
    (agreement : ∀ point : ClosedDisk, point.val ∈ openUnitDisk → first point = second point) :
    first = second := by
  apply ContinuousMap.ext
  have equality := openDisk_dense.equalizer first.continuous second.continuous (by
    funext point
    exact agreement (openDiskInclusion point) point.property)
  exact congrFun equality

theorem continuousMap_eq_of_openDiskCell
    {Target : Type*} [TopologicalSpace Target] [T2Space Target]
    (first second : ContinuousMap DiskCellDomain Target)
    (agreement : ∀ point : DiskCellDomain, point.1.val ∈ openUnitDisk → first point = second point) :
    first = second := by
  apply ContinuousMap.ext
  have equality := openDiskCell_dense.equalizer first.continuous second.continuous (by
    funext point
    exact agreement (openDiskCellInclusion point) point.1.property)
  exact congrFun equality

theorem disk_topology_goal : DiskTopologyGoal :=
  ⟨openDiskMembershipClosed, openDisk_dense⟩

theorem disk_cell_topology_goal : DiskCellTopologyGoal := openDiskCell_dense

end Grad.ClosedJets
