import AKBT13SameNativeRowsPhase
import AKBL29LiteralFixedGaugeMeans

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

/-- The scalar mean removal commutes with selection of the actual axial
cell by Fubini, retaining every angular and axial mode. -/
theorem nativeScalarMean_axialCell (field : ℝ × ℝ → ComplexEuclidean 1)
    (continuousField : Continuous field) (cell : ℤ) (angle : ℝ) :
    angularCoefficient (fun axial => removePolarMean field (angle,axial)) cell =
      angularCoefficient (fun axial => field (angle,axial)) cell -
        angularCoefficient (fun polar => angularCoefficient (fun axial => field (polar,axial)) cell) 0 := by
  have continuousMean : Continuous (fun axial => angularCoefficient (fun polar => field (polar,axial)) 0) :=
    Grad.SourceCollarFullSource.angularCoefficient_continuous_parameter (fun angles => field (angles.2,angles.1))
      (continuousField.comp (continuous_snd.prodMk continuous_fst)) 0
  have subtraction := angularCoefficient_sub_general (fun axial => field (angle,axial))
    (fun axial => angularCoefficient (fun polar => field (polar,axial)) 0)
    (continuousField.comp (continuous_const.prodMk continuous_id)) continuousMean cell
  exact subtraction.trans (congrArg (angularCoefficient (fun axial => field (angle,axial)) cell - ·)
    (doubleCoefficient_swap field continuousField 0 cell).symm)

theorem nativeScalarMean_localCell {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1) (cell : ℤ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (angle : ℝ) :
    curves.meanFree.cartesianCellField bounded cell (spatialPlaneOfPair (polarCoord.symm (radius,angle))) =
      curves.cartesianCellField bounded cell (spatialPlaneOfPair (polarCoord.symm (radius,angle))) -
        angularCoefficient (fun polar => curves.cartesianCellField bounded cell
          (spatialPlaneOfPair (polarCoord.symm (radius,polar)))) 0 := by
  rw [curves.meanFree.cartesianCellField_actual bounded cell radius inside angle,
    curves.cartesianCellField_actual bounded cell radius inside angle]
  simp_rw [curves.cartesianCellField_actual bounded cell radius inside,
    curves.fullField_meanFree bounded radius inside]
  exact nativeScalarMean_axialCell _ (curves.fullField_continuous_angles bounded radius inside) cell angle

variable (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index, 0 < lower index) (bounded : ∀ index, lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index, DivisionRow 1 (lower index))
    (curves : ∀ index, SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction 1 (lower second) (lower first) (decreasing ordered) (rows second) = rows first)
include compatible

theorem nativeScalarMean_gluedPolar (cell : ℤ) (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc (lower index) 1) (angle : ℝ) :
    gluedCartesianCellField parameters lower positive bounded cofinal
      (fun index => meanFreeRow (lower index) (rows index)) (fun index => (curves index).meanFree)
      cell (spatialPlaneOfPair (polarCoord.symm (radius,angle))) =
      gluedCartesianCellField parameters lower positive bounded cofinal rows curves
        cell (spatialPlaneOfPair (polarCoord.symm (radius,angle))) -
      angularCoefficient (fun polar => gluedCartesianCellField parameters lower positive bounded cofinal rows curves
        cell (spatialPlaneOfPair (polarCoord.symm (radius,polar)))) 0 := by
  have meanCompatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction 1 (lower second) (lower first) (decreasing ordered)
        (meanFreeRow (lower second) (rows second)) = meanFreeRow (lower first) (rows first) := by
    intro first second ordered
    rw [originalBulkRestriction_meanFree,compatible first second ordered]
  have localSame (polar : ℝ) := gluedCartesianCellField_same parameters lower positive bounded cofinal
    decreasing rows curves compatible cell index (spatialPlaneOfPair (polarCoord.symm (radius,polar)))
    (by simpa only [spatialPlaneOfPair_polar_norm radius polar ((positive index).le.trans inside.1)] using inside)
  rw [gluedCartesianCellField_same parameters lower positive bounded cofinal decreasing _ _ meanCompatible cell index _
    (by simpa only [spatialPlaneOfPair_polar_norm radius angle ((positive index).le.trans inside.1)] using inside)]
  simp_rw [localSame]
  exact nativeScalarMean_localCell (curves index) (bounded index) cell radius inside angle

end Grad.ActualScaledNativeCoefficients
