import AKAE6ExactPhysicalCellFields

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualCartesianDescent
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceBoundaryTrace
open Grad.ActualSmoothPhysicalField Grad.AnnularRestriction Grad.DiskExtension.Operator Grad.BoundaryTrace

variable {dimension : ℕ} (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow dimension (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction dimension (lower second) (lower first) (decreasing ordered) (rows second)=rows first)

include compatible in
theorem projectedPhysicalFamily_compatible (cell : ℤ) (first second : ℕ) (ordered : first ≤ second) :
    originalBulkRestriction dimension (lower second) (lower first) (decreasing ordered)
      (cellPhysicalRow (lower second) cell (rows second)) = cellPhysicalRow (lower first) cell (rows first) := by
  rw [cellPhysicalRow_restriction,compatible first second ordered]

def gluedCartesianCellField (cell : ℤ) (point : SpatialPlane) : ComplexEuclidean dimension :=
  gluedCartesianFamilyField parameters lower positive bounded cofinal
    (fun index => cellPhysicalRow (lower index) cell (rows index))
    (fun index => (curves index).cellProjection cell) (point,0)

include compatible in
theorem gluedCartesianCellField_same (cell : ℤ) (index : ℕ) (point : SpatialPlane)
    (inside : ‖point‖ ∈ Icc (lower index) 1) :
    gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell point =
      (curves index).cartesianCellField (bounded index) cell point :=
  gluedCartesianFamilyField_same parameters lower positive bounded cofinal decreasing
    (fun index => cellPhysicalRow (lower index) cell (rows index))
    (fun index => (curves index).cellProjection cell)
    (projectedPhysicalFamily_compatible lower decreasing rows compatible cell) index (point,0) inside

include compatible in
theorem gluedCartesianCellField_smoothAt (cell : ℤ) (point : SpatialPlane) (nonzero : point ≠ 0) (inside : ‖point‖ < 1) :
    ContDiffAt ℝ ∞ (gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell) point :=
  (gluedCartesianFamilyField_smoothAt parameters lower positive bounded cofinal decreasing
    (fun index => cellPhysicalRow (lower index) cell (rows index))
    (fun index => (curves index).cellProjection cell)
    (projectedPhysicalFamily_compatible lower decreasing rows compatible cell) (point,0) nonzero inside).comp point
    (contDiffAt_id.prodMk contDiffAt_const)

include compatible in
theorem gluedCartesianCellField_coefficient (cell : ℤ) (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc (lower index) 1) (angular : ℤ) :
    angularCoefficient (fun polar => gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell
      (spatialPlaneOfPair (polarCoord.symm (radius,polar)))) angular =
        gluedPhysicalFamilyCurve parameters lower positive bounded cofinal rows curves 0 radius (angular,cell) := by
  have same (polar : ℝ) : gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell
      (spatialPlaneOfPair (polarCoord.symm (radius,polar))) =
      (curves index).cartesianCellField (bounded index) cell (spatialPlaneOfPair (polarCoord.symm (radius,polar))) :=
    gluedCartesianCellField_same parameters lower positive bounded cofinal decreasing rows curves compatible cell index _
      (by simpa only [spatialPlaneOfPair_polar_norm radius polar ((positive index).le.trans inside.1)] using inside)
  simp_rw [same]
  rw [(curves index).cartesianCellField_coefficient (bounded index) cell radius inside angular,
    gluedPhysicalFamilyCurve_same parameters lower positive bounded cofinal decreasing rows curves compatible 0 index radius inside]

end Grad.ActualCartesianDescent
