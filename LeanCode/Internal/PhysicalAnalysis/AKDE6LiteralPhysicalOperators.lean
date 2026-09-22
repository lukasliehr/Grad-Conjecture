import AKDE5OriginalPhysicalDerivatives
import RealComplexification

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 3500
open Set Filter
open scoped ContDiff Topology

namespace Grad.OriginalCellFamily
open Grad.CartesianState Grad.ClosedJets Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.OriginalParameterEvaluation Grad.OriginalCoreRealization Grad.DiskExtension.Operator
open Grad.PhysicalFamily Grad.AxisSplit

variable {dimension : ℕ} {parameters : PhaseParameters}

def originalCellField (field : ACore parameters dimension) : SpatialPlane → ℝ → ComplexEuclidean dimension :=
  fun point cell => originalProductField field (point,cell)

theorem originalCellField_spatial_fderiv (field : ACore parameters dimension) (point : SpatialPlane)
    (cell : ℝ) (direction : SpatialPlane) :
    fderiv ℝ (fun query => originalCellField field query cell) point direction =
      fderiv ℝ (originalProductField field) (point,cell) (direction,0) := by
  have insertion : HasFDerivAt (fun query : SpatialPlane => (query,cell))
      (ContinuousLinearMap.inl ℝ SpatialPlane ℝ) point := by
    exact (hasFDerivAt_id point).prodMk (hasFDerivAt_const cell point)
  have composed := ((originalProductField_smooth field).differentiable (by simp)).differentiableAt.hasFDerivAt.comp point insertion
  exact congrArg (fun derivative : SpatialPlane →L[ℝ] ComplexEuclidean dimension => derivative direction) composed.fderiv

theorem originalCellField_cellDerivative (field : ACore parameters dimension)
    (point : ClosedDisk) (cell : ℝ) :
    cellDerivative (originalCellField field) point.val cell = originalCellField (timeDerivativeCore parameters field) point.val cell := by
  have insertion : HasFDerivAt (fun query : ℝ => (point.val,query))
      (ContinuousLinearMap.inr ℝ SpatialPlane ℝ) cell := by
    exact (hasFDerivAt_const point.val cell).prodMk (hasFDerivAt_id cell)
  have composed := ((originalProductField_smooth field).differentiable (by simp)).differentiableAt.hasFDerivAt.comp cell insertion
  unfold cellDerivative
  change fderiv ℝ (originalProductField field ∘ fun query => (point.val,query)) cell 1 = _
  rw [composed.fderiv]
  exact originalProductField_axial field point cell

private theorem originalPlane_basis (point : SpatialPlane) :
    point = point 0 • spatialBasis 0 + point 1 • spatialBasis 1 := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [spatialBasis]

/-- Literal Euler action of the unchanged original core on the full closed disk. -/
theorem originalCellField_euler (field : ACore parameters dimension)
    (point : ClosedDisk) (cell : ℝ) :
    diskEuler (originalCellField field) point.val cell = originalCellField (eulerCore parameters field) point.val cell := by
  unfold diskEuler
  rw [originalCellField_spatial_fderiv]
  have split : (point.val,(0:ℝ)) = point.val 0 • (spatialBasis 0,(0:ℝ)) + point.val 1 • (spatialBasis 1,(0:ℝ)) := by
    apply Prod.ext
    · exact originalPlane_basis point.val
    · simp
  rw [split,map_add,map_smul,map_smul,originalProductField_partial,originalProductField_partial]
  change _ = originalExtendedField parameters (eulerCore parameters field) (assembleSpatialCell point.val cell)
  rw [originalExtendedField_coreValue]
  change _ = coreValue (coordinateCore parameters 0 (partialCore parameters 0 field) +
    coordinateCore parameters 1 (partialCore parameters 1 field)) point cell
  rw [coreValue_add,coreValue_coordinate,coreValue_coordinate]
  change point.val 0 • originalExtendedField parameters (partialCore parameters 0 field) (assembleSpatialCell point.val cell) +
    point.val 1 • originalExtendedField parameters (partialCore parameters 1 field) (assembleSpatialCell point.val cell) = _
  rw [originalExtendedField_coreValue,originalExtendedField_coreValue]

/-- Literal angular action of the unchanged original core on the full closed disk. -/
theorem originalCellField_rotation (field : ACore parameters dimension)
    (point : ClosedDisk) (cell : ℝ) :
    diskAngular (originalCellField field) point.val cell = originalCellField (rotationCore parameters field) point.val cell := by
  unfold diskAngular
  rw [originalCellField_spatial_fderiv]
  have split : (planeQuarterTurn point.val,(0:ℝ)) = point.val 0 • (spatialBasis 1,(0:ℝ)) - point.val 1 • (spatialBasis 0,(0:ℝ)) := by
    apply Prod.ext
    · apply PiLp.ext
      intro coordinate
      fin_cases coordinate <;> simp [planeQuarterTurn,spatialBasis]
    · simp
  rw [split,map_sub,map_smul,map_smul,originalProductField_partial,originalProductField_partial]
  change _ = originalExtendedField parameters (rotationCore parameters field) (assembleSpatialCell point.val cell)
  rw [originalExtendedField_coreValue]
  change _ = coreValue (coordinateCore parameters 0 (partialCore parameters 1 field) -
    coordinateCore parameters 1 (partialCore parameters 0 field)) point cell
  rw [Grad.GaugeCoefficients.Physical.RadialLedger.coreValue_subtract,coreValue_coordinate,coreValue_coordinate]
  change point.val 0 • originalExtendedField parameters (partialCore parameters 1 field) (assembleSpatialCell point.val cell) -
    point.val 1 • originalExtendedField parameters (partialCore parameters 0 field) (assembleSpatialCell point.val cell) = _
  rw [originalExtendedField_coreValue,originalExtendedField_coreValue]

end Grad.OriginalCellFamily
