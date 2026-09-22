import AKAH5ActualSourcePhysicalIntegrability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualCartesianFlux
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.ActualSmoothPhysicalField Grad.ActualPhysicalField Grad.ActualCartesianDescent
open Grad.ActualCartesianIntegrability Grad.AnnularRestriction Grad.DiskExtension.Operator Grad.BoundaryTrace
open Grad.SourceCollarFullSource
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger

variable {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (lower : ℕ → ℝ)
    (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow input (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction input (lower second) (lower first) (decreasing ordered) (rows second)=rows first)

/-- The literal completed coefficient action retains every angular and axial cell. -/
def matrixFluxRows (index : ℕ) : DivisionRow output (lower index) :=
  originalMatrixBulkAction parameters family coherent 0 (lower index) (positive index) (bounded index).le (rows index)

def matrixFluxCurves (index : ℕ) : SmoothLowPhysicalRow parameters (lower index) (positive index)
    (matrixFluxRows parameters family coherent lower positive bounded rows index) :=
  (curves index).matrixAction parameters family coherent (lower index) (positive index) (bounded index)

include compatible in
theorem matrixFluxRows_compatible (first second : ℕ) (ordered : first ≤ second) :
    originalBulkRestriction output (lower second) (lower first) (decreasing ordered)
      (matrixFluxRows parameters family coherent lower positive bounded rows second) =
        matrixFluxRows parameters family coherent lower positive bounded rows first := by
  unfold matrixFluxRows
  rw [originalMatrixBulkAction_restriction,compatible first second ordered]

def matrixFluxCell (cell : ℤ) : SpatialPlane → ComplexEuclidean output :=
  gluedCartesianCellField parameters lower positive bounded cofinal
    (matrixFluxRows parameters family coherent lower positive bounded rows)
    (matrixFluxCurves parameters family coherent lower positive bounded rows curves) cell

include compatible in
/-- Native energy controls the full convolution flux, including coefficient-dependent axial mixing. -/
theorem matrixFluxCell_integrable_pair (K : ℝ) (estimate : ∀ index,‖rows index‖ ≤ K) (cell : ℤ) :
    IntegrableOn (matrixFluxCell parameters family coherent lower positive bounded cofinal rows curves cell) openUnitDisk ∧
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖matrixFluxCell parameters family coherent lower positive bounded cofinal rows curves cell point‖) openUnitDisk := by
  apply sameOriginalPhysicalCell_integrable_pair parameters lower positive bounded cofinal decreasing
    (matrixFluxRows parameters family coherent lower positive bounded rows)
    (matrixFluxCurves parameters family coherent lower positive bounded rows curves)
    (matrixFluxRows_compatible parameters family coherent lower positive bounded decreasing rows compatible)
    (Grad.ActualPhysicalField.physicalMatrixKernelConstant parameters input output 0 * ‖family 1‖ * K)
  intro index
  exact (originalMatrixBulkAction_bound parameters family coherent 0 (lower index) (positive index) (bounded index).le (rows index)).trans
    (mul_le_mul_of_nonneg_left (estimate index) (mul_nonneg
      (physicalMatrixKernelConstant_nonnegative parameters input output 0) (norm_nonneg _)))

include compatible in
/-- The flux cell is the axial coefficient of the literal matrix product of the SAME full field. -/
theorem matrixFluxCell_actual (cell : ℤ) (index : ℕ) (radius : ℝ) (inside : radius ∈ Icc (lower index) 1) (polar : ℝ) :
    matrixFluxCell parameters family coherent lower positive bounded cofinal rows curves cell
      (spatialPlaneOfPair (polarCoord.symm (radius,polar))) =
      angularCoefficient (fun axial => WithLp.toLp 2
        ((familyMatrix family 0 axial (polarClosedPoint radius polar ((positive index).le.trans inside.1) inside.2)).mulVec
          ((curves index).fullField (bounded index) (radius,polar,axial)))) cell := by
  rw [matrixFluxCell,gluedCartesianCellField_same parameters lower positive bounded cofinal decreasing
    (matrixFluxRows parameters family coherent lower positive bounded rows)
    (matrixFluxCurves parameters family coherent lower positive bounded rows curves)
    (matrixFluxRows_compatible parameters family coherent lower positive bounded decreasing rows compatible)
    cell index _ (by simpa only [spatialPlaneOfPair_polar_norm radius polar ((positive index).le.trans inside.1)] using inside)]
  rw [SmoothLowPhysicalRow.cartesianCellField_actual (matrixFluxCurves parameters family coherent lower positive bounded rows curves index)
    (bounded index) cell radius inside polar]
  congr 1
  funext axial
  exact ((curves index).fullField_matrixAction parameters family coherent (lower index) (positive index) (bounded index) radius inside (polar,axial)).trans
    (physicalMatrixProduct_apply parameters family radius ((positive index).le.trans inside.1) inside.2 _ (polar,axial))

end Grad.ActualCartesianFlux
