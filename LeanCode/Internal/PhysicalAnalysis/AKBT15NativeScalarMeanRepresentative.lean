import AKBT14NativeScalarMeanCells

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace Grad.ActualScaledNativeCoefficients
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.BoundaryTrace
open Grad.SourceCollarCoefficients Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.ActualSmoothPhysicalField Grad.ActualCartesianDescent Grad.ActualPuncturedFamily
open Grad.AnnularRestriction Grad.DiskExtension.Operator Grad.SourceCollarFullSource
open Grad.CartesianStartup Grad.GenericCarriers Grad.SpatialDilation Grad.ActualCartesianWeakEquations
open Grad.GaugeCoefficients.Physical.RadialLedger

variable (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index, 0 < lower index) (bounded : ∀ index, lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index, DivisionRow 1 (lower index))
    (curves : ∀ index, SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction 1 (lower second) (lower first) (decreasing ordered) (rows second) = rows first)
include compatible

theorem nativeScalarMean_closed (cell : ℤ) (point : ClosedDisk) (nonzero : point.val ≠ 0)
    (inside : ‖point.val‖ < 1) :
    gluedCartesianCellField parameters lower positive bounded cofinal
      (fun index => meanFreeRow (lower index) (rows index)) (fun index => (curves index).meanFree) cell point.val =
      gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell point.val -
      closedCharacterProjection 0
        (fun closed => gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell closed.val) point := by
  obtain ⟨angle,polar⟩ := closedPoint_has_polar_angle point
  have represented (query : ℝ) :
      spatialPlaneOfPair (polarCoord.symm (‖point.val‖,query)) =
        (Grad.Constraints.polarClosedPoint ‖point.val‖ (by rw [abs_norm]; exact point.property) query).val := by
    rw [polarPlane_originalParametrization,Grad.Constraints.polarClosedPoint_coordinates]
    ext coordinate
    fin_cases coordinate <;> simp [polarPlane,collarPlane]
  let index := selectedInnerCollar lower cofinal ‖point.val‖ (norm_pos_iff.mpr nonzero)
  have collar : ‖point.val‖ ∈ Icc (lower index) 1 :=
    ⟨(selectedInnerCollar_lt lower cofinal ‖point.val‖ (norm_pos_iff.mpr nonzero)).le,inside.le⟩
  have actual := nativeScalarMean_gluedPolar parameters lower positive bounded cofinal decreasing rows curves compatible
    cell index ‖point.val‖ collar angle
  simp_rw [represented] at actual
  rw [polar] at actual
  rw [← polar,startupClosedScalarMean_polar,polar]
  exact actual

/-- The original scalar projector acts on the SAME full native L2 field.
No continuous representative at the axis is assumed. -/
theorem nativeScalarMean_L2 (field : StartupL2 1)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      field point cell = gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell point) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      originalScalarMeanFreeKernel field point cell =
        gluedCartesianCellField parameters lower positive bounded cofinal
          (fun index => meanFreeRow (lower index) (rows index)) (fun index => (curves index).meanFree) cell point := by
  have each (cell : ℤ) := startupCharacter_closedRepresentative 0 field cell
    (fun closed => gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell closed.val) (by
      filter_upwards [same,ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point actual inside
      exact (actual cell).trans (closedFieldExtension_value
        (fun closed => gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell closed.val)
        ⟨point,openDiskMembershipClosed point inside⟩).symm)
  filter_upwards [ae_all_iff.mpr each,same,startupDisk_ae_nonzero,
    Lp.coeFn_sub field (startupCharacterKernel 1 0 field),ae_restrict_mem openUnitDisk_isOpen.measurableSet]
    with point projected actual nonzero subtraction inside
  intro cell
  change (field-startupCharacterKernel 1 0 field) point cell = _
  rw [subtraction,Pi.sub_apply,lp.coeFn_sub,Pi.sub_apply,actual cell,projected cell]
  rw [closedFieldExtension_value _ ⟨point,openDiskMembershipClosed point inside⟩]
  exact (nativeScalarMean_closed parameters lower positive bounded cofinal decreasing rows curves compatible
    cell ⟨point,openDiskMembershipClosed point inside⟩ nonzero inside).symm

end Grad.ActualScaledNativeCoefficients
