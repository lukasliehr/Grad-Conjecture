import AKBE21RadialProjectionAxialCell

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace Grad.ActualCartesianWeakEquations
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.BoundaryTrace
open Grad.SourceCollarCoefficients Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.ActualSmoothPhysicalField Grad.ActualCartesianDescent Grad.ActualPuncturedFamily
open Grad.AnnularRestriction Grad.DiskExtension.Operator Grad.SourceCollarFullSource

variable {dimension : ℕ} (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index, 0 < lower index) (bounded : ∀ index, lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index, DivisionRow dimension (lower index))
    (curves : ∀ index, SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction dimension (lower second) (lower first) (decreasing ordered) (rows second) = rows first)
include compatible

/-- The existing compatible cell reconstruction is the Fourier cell of
its SAME full Cartesian field at every interior nonzero point. -/
theorem nativeFamilyCell_actual (cell : ℤ) (point : Spatial) (nonzero : point ≠ 0) (inside : ‖point‖ < 1) :
    gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell point =
      angularCoefficient (fun axial => gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves (point,axial)) cell := by
  let closed : ClosedDisk := ⟨point,by change ‖point‖ ≤ 1; exact inside.le⟩
  obtain ⟨angle,polar⟩ := closedPoint_has_polar_angle closed
  have represented : spatialPlaneOfPair (polarCoord.symm (‖point‖,angle)) = point := by
    rw [polarPlane_originalParametrization]
    have coordinates := congrArg Subtype.val polar
    rw [Grad.Constraints.polarClosedPoint_coordinates] at coordinates
    simpa [polarPlane,collarPlane,closed] using coordinates
  let index := selectedInnerCollar lower cofinal ‖point‖ (norm_pos_iff.mpr nonzero)
  have collar : ‖point‖ ∈ Icc (lower index) 1 :=
    ⟨(selectedInnerCollar_lt lower cofinal ‖point‖ (norm_pos_iff.mpr nonzero)).le,inside.le⟩
  have actual := gluedCartesianCellField_actual_polar parameters lower positive bounded cofinal decreasing rows curves compatible
    cell index ‖point‖ collar angle
  simpa only [represented] using actual

 theorem nativeFamilyField_smooth :
    ContDiffOn ℝ ∞ (gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves)
      ((openUnitDisk \ {(0 : Spatial)}) ×ˢ (univ : Set ℝ)) := by
  intro point inside
  exact (gluedCartesianFamilyField_smoothAt parameters lower positive bounded cofinal decreasing rows curves compatible point
    (by simpa only [mem_singleton_iff] using inside.1.2) inside.1.1).contDiffWithinAt

/-- Actual Cartesian derivatives of the SAME cell are exactly axial
coefficients of derivatives of the original glued physical field. -/
theorem nativeFamilyCell_fderiv_apply (cell : ℤ) (point : Spatial) (nonzero : point ≠ 0)
    (inside : ‖point‖ < 1) (direction : Spatial) :
    fderiv ℝ (gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell) point direction =
      angularCoefficient (fun axial =>
        fderiv ℝ (gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves) (point,axial) (direction,0)) cell := by
  let domain : Set Spatial := openUnitDisk \ {(0 : Spatial)}
  have openDomain : IsOpen domain := openUnitDisk_isOpen.sdiff isClosed_singleton
  have member : point ∈ domain := ⟨inside,by simpa only [mem_singleton_iff] using nonzero⟩
  have same : gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell =ᶠ[𝓝 point]
      (fun current => angularCoefficient (fun axial => gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves
        (current,axial)) cell) := by
    filter_upwards [openDomain.mem_nhds member] with current membership
    exact nativeFamilyCell_actual parameters lower positive bounded cofinal decreasing rows curves compatible cell current
      (by simpa only [mem_singleton_iff] using membership.2) membership.1
  rw [same.fderiv_eq,originalCell_fderiv_apply openDomain _
    (nativeFamilyField_smooth parameters lower positive bounded cofinal decreasing rows curves compatible) cell point member direction]
  congr 1

end Grad.ActualCartesianWeakEquations
