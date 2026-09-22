import AKBK1SameGlobalCellDerivatives
import AKBK8NativeForceMatrixCells

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

/-- Native cell smoothness reuses the accepted compatible Cartesian gluer. -/
theorem nativeFamilyCell_smooth (cell : ℤ) :
    ContDiffOn ℝ ∞ (gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell)
      (openUnitDisk \ {(0 : Spatial)}) := by
  intro point inside
  exact (gluedCartesianCellField_smoothAt parameters lower positive bounded cofinal decreasing rows curves compatible
    cell point (by simpa only [mem_singleton_iff] using inside.2) inside.1).contDiffWithinAt

/-- Multiplication by radius gives the SAME native Xi cell and is smooth away from the axis. -/
theorem nativeRadiusCell_smooth (cell : ℤ) :
    ContDiffOn ℝ ∞ (fun point => ‖point‖ • gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell point)
      (openUnitDisk \ {(0 : Spatial)}) := by
  intro point inside
  have radiusSmooth : ContDiffAt ℝ ∞ (fun current : Spatial => ‖current‖) point := contDiffAt_norm ℝ (show point ≠ 0 by simpa only [mem_singleton_iff] using inside.2)
  exact radiusSmooth.contDiffWithinAt.smul
    (nativeFamilyCell_smooth parameters lower positive bounded cofinal decreasing rows curves compatible cell point inside)

end Grad.ActualCartesianWeakEquations
