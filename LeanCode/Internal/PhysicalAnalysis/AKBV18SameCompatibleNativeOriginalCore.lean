import AKBV17LocalizedAllOrderOriginalCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace Grad.CartesianCoreRecovery
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.CartesianStartup
open Grad.WeightedJets Grad.BoundaryTrace Grad.SourceCollarDivision Grad.ActualSmoothPhysicalField
open Grad.ActualCartesianDescent Grad.ActualPuncturedFamily Grad.AnnularRestriction Grad.DiskExtension.Operator Grad.Constraints

theorem nativeCartesianCell_fullField {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1) (cell : ℤ) (point : SpatialPlane) (inside : ‖point‖ ∈ Icc lower 1) :
    curves.cartesianCellField bounded cell point =
      angularCoefficient (fun axial => curves.cartesianField bounded (point,axial)) cell := by
  simp only [SmoothLowPhysicalRow.cartesianCellField,SmoothLowPhysicalRow.cartesianField,
    cartesianPhysicalField,cartesianFromPolar,Grad.BoundaryLift.complexCoordinate_norm]
  rw [curves.fullField_cellProjection bounded cell ‖point‖ inside ((signedComplexCoordinate 1 point).arg,0)]
  simp [cellExponential]

variable {dimension : ℕ} (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow dimension (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction dimension (lower second) (lower first) (decreasing ordered) (rows second)=rows first)

include compatible in
theorem compatibleNativeCell_continuous (cell : ℤ) :
    ContinuousOn (gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell)
      {point : SpatialPlane | 0 < ‖point‖ ∧ ‖point‖ < 1} := by
  intro point inside
  exact (gluedCartesianCellField_smoothAt parameters lower positive bounded cofinal decreasing rows curves compatible
    cell point (norm_pos_iff.mp inside.1) inside.2).continuousAt.continuousWithinAt

include compatible in
theorem compatibleNativeCell_collar (index : ℕ) (point : SpatialPlane) (inside : ‖point‖ ∈ Icc (lower index) 1) (cell : ℤ) :
    gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell point =
      angularCoefficient (fun axial => (curves index).cartesianField (bounded index) (point,axial)) cell :=
  (gluedCartesianCellField_same parameters lower positive bounded cofinal decreasing rows curves compatible cell index point inside).trans
    (nativeCartesianCell_fullField (curves index) (bounded index) cell point inside)

include compatible in
/-- Exact compatible native reconstruction from the localized all-order Sobolev output. The only regularity input is the standard all-order graph of the SAME weighted carrier. -/
theorem compatibleLocalizedAllOrder_originalCore
    (scale upper : ℝ) (scalePositive : 0 < scale) (upperPositive : 0 < upper)
    (upperScale : upper ≤ scale) (upperOne : upper ≤ 1)
    (field : StartupL2 dimension) (jets : ∀ grade, GraphGrade dimension grade grade openUnitDisk)
    (sameBase : ∀ grade, base dimension grade openUnitDisk (fun _ => grade) (jets grade) = field)
    (cutoff : SpatialPlane → ℝ) (cutoffOne : ∀ point, scale * ‖point‖ < upper → cutoff point = 1)
    (sameRaw : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      field point cell = cutoff point • (cartesianWeight parameters cell (scale • point) •
        gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell (scale • point))) :
    ∃ core : ACore parameters dimension, ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ cell : ℤ,
      (core.val cell).value point = gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell point.val := by
  let index := selectedInnerCollar lower cofinal upper upperPositive
  have below : lower index < upper := selectedInnerCollar_lt lower cofinal upper upperPositive
  exact localizedAllOrder_sameOriginalCore parameters (lower index) (positive index) (bounded index) (rows index) (curves index)
    scale upper scalePositive below upperScale upperOne field jets sameBase
    (gluedCartesianCellField parameters lower positive bounded cofinal rows curves)
    (compatibleNativeCell_continuous parameters lower positive bounded cofinal decreasing rows curves compatible)
    (compatibleNativeCell_collar parameters lower positive bounded cofinal decreasing rows curves compatible index)
    cutoff cutoffOne sameRaw

end Grad.CartesianCoreRecovery
