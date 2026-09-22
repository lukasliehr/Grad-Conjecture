import AKBT15NativeScalarMeanRepresentative

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
open Grad.GaugeCoefficients.Physical.Ledger Grad.AnnularCurrentEnergy

theorem nativeValue_localCell {dimension output : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1) (target : Fin output) (source : Fin dimension)
    (cell : ℤ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (angle : ℝ) :
    (curves.bulkUnit target source).cartesianCellField bounded cell (spatialPlaneOfPair (polarCoord.symm (radius,angle))) =
      matrixUnit target source (curves.cartesianCellField bounded cell (spatialPlaneOfPair (polarCoord.symm (radius,angle)))) := by
  rw [(curves.bulkUnit target source).cartesianCellField_actual bounded cell radius inside angle,
    curves.cartesianCellField_actual bounded cell radius inside angle]
  simp_rw [curves.fullField_bulkUnit bounded target source radius inside]
  exact startupAngularCoefficient_clm (matrixUnit target source)
    (fun axial => curves.fullField bounded (radius,angle,axial))
    ((curves.fullField_continuous_angles bounded radius inside).comp (continuous_const.prodMk continuous_id)) cell

variable {dimension output : ℕ} (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index, 0 < lower index) (bounded : ∀ index, lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index, DivisionRow dimension (lower index))
    (curves : ∀ index, SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction dimension (lower second) (lower first) (decreasing ordered) (rows second) = rows first)
include compatible

theorem nativeValue_gluedCell (target : Fin output) (source : Fin dimension)
    (cell : ℤ) (point : Spatial) (nonzero : point ≠ 0) (inside : ‖point‖ < 1) :
    gluedCartesianCellField parameters lower positive bounded cofinal
      (fun index => bulkMatrixUnit (lower index) target source (rows index))
      (fun index => (curves index).bulkUnit target source) cell point =
    matrixUnit target source (gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell point) := by
  let closed : ClosedDisk := ⟨point,inside.le⟩
  obtain ⟨angle,polar⟩ := closedPoint_has_polar_angle closed
  have represented : spatialPlaneOfPair (polarCoord.symm (‖point‖,angle)) = point := by
    rw [polarPlane_originalParametrization]
    have coordinates := congrArg Subtype.val polar
    rw [Grad.Constraints.polarClosedPoint_coordinates] at coordinates
    simpa [polarPlane,collarPlane,closed] using coordinates
  let index := selectedInnerCollar lower cofinal ‖point‖ (norm_pos_iff.mpr nonzero)
  have collar : ‖point‖ ∈ Icc (lower index) 1 :=
    ⟨(selectedInnerCollar_lt lower cofinal ‖point‖ (norm_pos_iff.mpr nonzero)).le,inside.le⟩
  have valueCompatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction output (lower second) (lower first) (decreasing ordered)
        (bulkMatrixUnit (lower second) target source (rows second)) = bulkMatrixUnit (lower first) target source (rows first) := by
    intro first second ordered
    rw [bulkMatrixUnit_restriction,compatible first second ordered]
  rw [gluedCartesianCellField_same parameters lower positive bounded cofinal decreasing _ _ valueCompatible cell index point collar,
    gluedCartesianCellField_same parameters lower positive bounded cofinal decreasing rows curves compatible cell index point collar]
  rw [← represented]
  exact nativeValue_localCell (curves index) (bounded index) target source cell ‖point‖ collar angle

theorem nativeValue_L2 (target : Fin output) (source : Fin dimension) (field : StartupL2 dimension)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      field point cell = gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell point) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      originalValueKernel (matrixUnit target source) field point cell =
        gluedCartesianCellField parameters lower positive bounded cofinal
          (fun index => bulkMatrixUnit (lower index) target source (rows index))
          (fun index => (curves index).bulkUnit target source) cell point := by
  filter_upwards [startupPointKernel_field_ae (matrixUnit target source) (LinearIsometryEquiv.refl ℝ _) field,
    same,startupDisk_ae_nonzero,ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point mapped actual nonzero inside
  intro cell
  exact (mapped cell).trans ((congrArg (matrixUnit target source) (actual cell)).trans
    (nativeValue_gluedCell parameters lower positive bounded cofinal decreasing rows curves compatible
      target source cell point nonzero inside).symm)

end Grad.ActualScaledNativeCoefficients
