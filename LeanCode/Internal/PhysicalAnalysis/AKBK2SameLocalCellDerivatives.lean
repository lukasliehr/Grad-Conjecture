import AKBK1SameGlobalCellDerivatives

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

/-- The SAME cell uses the full local physical field on every strict collar. -/
theorem nativeFamilyCell_local (cell : ℤ) (index : ℕ) (point : Spatial)
    (inside : ‖point‖ ∈ Ioo (lower index) 1) :
    gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell point =
      angularCoefficient (fun axial => (curves index).cartesianField (bounded index) (point,axial)) cell := by
  rw [nativeFamilyCell_actual parameters lower positive bounded cofinal decreasing rows curves compatible cell point
    (norm_pos_iff.mp ((positive index).trans inside.1)) inside.2]
  congr 1
  funext axial
  exact gluedCartesianFamilyField_same parameters lower positive bounded cofinal decreasing rows curves compatible index (point,axial)
    ⟨inside.1.le,inside.2.le⟩

/-- The actual cell derivative is the Fourier coefficient of the genuine
local Cartesian derivative, in any direction, on each strict collar. -/
theorem nativeFamilyCell_fderiv_local (cell : ℤ) (index : ℕ) (point : Spatial)
    (inside : ‖point‖ ∈ Ioo (lower index) 1) (direction : Spatial) :
    fderiv ℝ (gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell) point direction =
      angularCoefficient (fun axial => fderiv ℝ ((curves index).cartesianField (bounded index))
        (point,axial) (direction,0)) cell := by
  rw [nativeFamilyCell_fderiv_apply parameters lower positive bounded cofinal decreasing rows curves compatible cell point
    (norm_pos_iff.mp ((positive index).trans inside.1)) inside.2 direction]
  congr 1
  funext axial
  rw [gluedCartesianFamilyField_fderiv_same parameters lower positive bounded cofinal decreasing rows curves compatible index (point,axial) inside]

end Grad.ActualCartesianWeakEquations
