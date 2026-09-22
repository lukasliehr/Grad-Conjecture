import P0910Continuity

noncomputable section

open Filter Set
open scoped BigOperators ContDiff Topology

namespace Grad.DiskExtension.Operator

open Grad.ClosedJets
open Grad.DiskExtension.Seeley

def retractedDiskCell (point : SpatialCell) : DiskCellDomain :=
  (radialRetraction (planarPart point), (point 2 : CellCircle))

theorem continuous_retractedDiskCell : Continuous retractedDiskCell := by
  have cellContinuous : Continuous
      (fun point : SpatialCell => (point 2 : CellCircle)) :=
    continuous_quotient_mk'.comp cellCoordinateCLM.continuous
  exact (continuous_radialRetraction.comp continuous_planarPart).prodMk cellContinuous

theorem retractedDiskCell_eq_diskCellPoint (point : SpatialCell)
    (membership : point ∈ closedUnitCylinder) :
    retractedDiskCell point = diskCellPoint point membership := by
  apply Prod.ext
  · apply Subtype.ext
    exact radialRetraction_val_of_mem (planarPart point) membership
  · rfl

theorem ambientExtensionCellLift_eq_if {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell) :
    ambientExtensionCellLift field point =
      if ‖planarPart point‖ ≤ 1 then field.value (retractedDiskCell point)
      else exteriorSeriesCellLift field point := by
  classical
  by_cases membership : ‖planarPart point‖ ≤ 1
  · have diskMembership : planarPart point ∈ closedUnitDisk := membership
    rw [if_pos membership, ambientExtensionCellLift, ambientExtensionFromValue,
      dif_pos diskMembership, retractedDiskCell_eq_diskCellPoint point membership]
    rfl
  · have diskMembership : planarPart point ∉ closedUnitDisk := membership
    rw [if_neg membership, ambientExtensionCellLift, ambientExtensionFromValue,
      dif_neg diskMembership]
    rfl

theorem ambientExtensionCellLift_continuous {dimension : ℕ}
    (field : DiskCellClosedJet dimension) :
    Continuous (ambientExtensionCellLift field) := by
  rw [show ambientExtensionCellLift field = fun point =>
      if ‖planarPart point‖ ≤ 1 then field.value (retractedDiskCell point)
      else exteriorSeriesCellLift field point by
    funext point
    exact ambientExtensionCellLift_eq_if field point]
  apply continuous_if_le (continuous_norm.comp continuous_planarPart) continuous_const
  · exact (field.value.continuous.comp continuous_retractedDiskCell).continuousOn
  · exact exteriorSeriesCellLift_continuousOn_outerClosed field
  · intro point boundary
    rw [retractedDiskCell_eq_diskCellPoint point boundary.le]
    exact (exteriorSeries_boundary field (planarPart point) boundary
      (point 2 : CellCircle)).symm

end Grad.DiskExtension.Operator
