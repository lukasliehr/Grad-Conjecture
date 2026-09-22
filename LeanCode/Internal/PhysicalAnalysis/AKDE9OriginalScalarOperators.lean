import AKDE8OriginalPhysicalMean
import RealLiteralRowsProof

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 3500
open Set
open scoped ContDiff

namespace Grad.OriginalCellFamily
open Grad.CartesianState Grad.ClosedJets Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.OriginalParameterEvaluation Grad.PhysicalFamily Grad.NonlinearQuotient

variable {parameters : PhaseParameters}

theorem originalCellField_spatial_smooth {dimension : ℕ} (field : ACore parameters dimension) (cell : ℝ) :
    ContDiff ℝ ∞ (fun point => originalCellField field point cell) :=
  (originalProductField_smooth field).comp (contDiff_id.prodMk contDiff_const)

theorem originalCellField_cell_smooth {dimension : ℕ} (field : ACore parameters dimension) (point : SpatialPlane) :
    ContDiff ℝ ∞ (originalCellField field point) :=
  (originalProductField_smooth field).comp (contDiff_const.prodMk contDiff_id)

def originalScalarProjection : ComplexEuclidean 1 →L[ℝ] ℂ :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).restrictScalars ℝ

theorem originalScalarCell_euler (field : ACore parameters 1) (point : ClosedDisk) (cell : ℝ) :
    diskEuler (originalScalarCell field) point.val cell = originalScalarCell (eulerCore parameters field) point.val cell := by
  have actual := diskEuler_postcompose originalScalarProjection (originalCellField field) point.val cell
    ((originalCellField_spatial_smooth field cell).differentiable (by simp)).differentiableAt
  change diskEuler (originalScalarCell field) point.val cell = originalScalarProjection (diskEuler (originalCellField field) point.val cell) at actual
  rw [actual,originalCellField_euler]
  rfl

theorem originalScalarCell_rotation (field : ACore parameters 1) (point : ClosedDisk) (cell : ℝ) :
    diskAngular (originalScalarCell field) point.val cell = originalScalarCell (rotationCore parameters field) point.val cell := by
  have actual := diskAngular_postcompose originalScalarProjection (originalCellField field) point.val cell
    ((originalCellField_spatial_smooth field cell).differentiable (by simp)).differentiableAt
  change diskAngular (originalScalarCell field) point.val cell = originalScalarProjection (diskAngular (originalCellField field) point.val cell) at actual
  rw [actual,originalCellField_rotation]
  rfl

theorem originalScalarCell_cellDerivative (field : ACore parameters 1) (point : ClosedDisk) (cell : ℝ) :
    cellDerivative (originalScalarCell field) point.val cell = originalScalarCell (timeDerivativeCore parameters field) point.val cell := by
  have actual := cellDerivative_postcompose originalScalarProjection (originalCellField field) point.val cell
    ((originalCellField_cell_smooth field point.val).differentiable (by simp)).differentiableAt
  change cellDerivative (originalScalarCell field) point.val cell = originalScalarProjection (cellDerivative (originalCellField field) point.val cell) at actual
  rw [actual,originalCellField_cellDerivative]
  rfl

theorem originalCellField_affine (length epsilon : ℝ) (vector : ACore parameters 3) (scalar : ACore parameters 1)
    (point : ClosedDisk) (cell : ℝ) :
    complexAffineStateDerivative length epsilon (originalCellField vector) point.val cell =
      originalCellField (affineStateCore parameters length ((epsilon:ℂ),vector,scalar)) point.val cell := by
  rw [complexAffineStateDerivative,originalCellField_cellDerivative]
  simp only [originalCellField_coreValue]
  change _ = coreValue (timeDerivativeCore parameters vector +
    (epsilon:ℂ) • valueMapCore parameters tangentGeneratorMap vector +
    (length:ℂ) • eTConstantCore parameters) point cell
  rw [coreValue_add,coreValue_add,coreValue_smul,coreValue_smul,coreValue_valueMap]
  change _ = coreValue (timeDerivativeCore parameters vector) point cell +
    (epsilon:ℂ) • tangentGeneratorMap (coreValue vector point cell) +
    (length:ℂ) • coreValue (constantCore parameters (EuclideanSpace.single 1 1)) point cell
  rw [coreValue_constant]
  simp only [Complex.coe_smul,tangentGeneratorMap_value]

end Grad.OriginalCellFamily
