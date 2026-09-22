import AKDE11ConstructedRealCellEquations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 3500
open Set
open scoped ContDiff

namespace Grad.OriginalCellFamily
open Grad.Constraints Grad.CartesianState Grad.ClosedJets Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.OriginalParameterEvaluation Grad.PhysicalFamily Grad.NonlinearQuotient Grad.AxisSplit

variable {parameters : PhaseParameters}

theorem realCellVector_spatial_fderiv (field : ACore parameters 3) (point : SpatialPlane)
    (cell : ℝ) (direction : SpatialPlane) :
    fderiv ℝ (fun query => realCellVector field query cell) point direction =
      physicalRealPart 3 (fderiv ℝ (originalProductField field) (point,cell) (direction,0)) := by
  have derivative := fderiv_postcompose (physicalRealPart 3) (fun query => originalCellField field query cell) point
    ((originalCellField_spatial_smooth field cell).differentiable (by simp)).differentiableAt
  change fderiv ℝ (fun query => realCellVector field query cell) point =
    (physicalRealPart 3).comp (fderiv ℝ (fun query => originalCellField field query cell) point) at derivative
  rw [derivative,ContinuousLinearMap.comp_apply,originalCellField_spatial_fderiv]

theorem coreValue_zeroJets_origin {dimension : ℕ} (field : ACore parameters dimension)
    (zeroJets : ∀ index, ZeroCartesianFirstJets (field.val index)) (cell : ℝ) :
    coreValue field originPoint cell = 0 := by
  have zero (index : ℤ) : (field.val index).value originPoint = 0 :=
    by simpa only [closedDerivative_zero_order, originPoint] using zeroJets index 0 (by omega) emptyCartesianWord
  unfold coreValue
  simp_rw [zero,smul_zero,tsum_zero]

theorem realCellVector_zeroJets_value (field : ACore parameters 3)
    (zeroJets : ∀ index, ZeroCartesianFirstJets (field.val index)) (cell : ℝ) :
    realCellVector field 0 cell = 0 := by
  change physicalRealPart 3 (originalCellField field originPoint.val cell) = 0
  rw [originalCellField_coreValue,coreValue_zeroJets_origin field zeroJets,map_zero]

theorem realCellVector_zeroJets_derivative (field : ACore parameters 3)
    (zeroJets : ∀ index, ZeroCartesianFirstJets (field.val index)) (cell : ℝ) :
    fderiv ℝ (fun point => realCellVector field point cell) 0 = 0 := by
  have coordinate (direction : Fin 2) :
      fderiv ℝ (fun point => realCellVector field point cell) 0 (spatialBasis direction) = 0 := by
    rw [realCellVector_spatial_fderiv]
    change physicalRealPart 3 (fderiv ℝ (originalProductField field) (originPoint.val,cell) (spatialBasis direction,0)) = 0
    rw [originalProductField_partial]
    change physicalRealPart 3 (originalExtendedField parameters (partialCore parameters direction field)
      (assembleSpatialCell originPoint.val cell)) = 0
    rw [originalExtendedField_coreValue,axisDerivative_zeroJets field zeroJets,map_zero]
  apply ContinuousLinearMap.ext
  intro direction
  have split : direction = direction 0 • spatialBasis 0 + direction 1 • spatialBasis 1 := by
    apply PiLp.ext
    intro index
    fin_cases index <;> simp [spatialBasis]
  rw [split,map_add,map_smul,map_smul,coordinate,coordinate,smul_zero,smul_zero,add_zero]
  rfl

/-- The actual tilt is the tangential part of the genuine first spatial
jet of the SAME normalized chart; it is not an independently chosen field. -/
theorem normalizedRealChart_tilt_firstJet (seed : Grad.Constraints.Seed.Parameters)
    (inside : seed ∈ Grad.Constraints.Seed.parameterDomain) (state : ChartState parameters)
    (zeroJets : ∀ index, ZeroCartesianFirstJets (state.2.1.val index))
    (direction : Fin 2) (cell : ℝ) :
    (fderiv ℝ (fun point => realCellVector (normalizedChart parameters seed inside state).1 point cell)
      0 (spatialBasis direction)) 1 = originalRealTilt state.1 cell direction := by
  rw [realCellVector_spatial_fderiv]
  change (physicalRealPart 3 (fderiv ℝ (originalProductField (normalizedChart parameters seed inside state).1)
    (originPoint.val,cell) (spatialBasis direction,0))) 1 = _
  rw [originalProductField_partial]
  change (physicalRealPart 3 (originalExtendedField parameters
    (partialCore parameters direction (normalizedChart parameters seed inside state).1)
      (assembleSpatialCell originPoint.val cell))) 1 = _
  rw [originalExtendedField_coreValue,normalizedChart_firstJet seed inside state zeroJets]
  simp [physicalRealPart,tamePlanarInclusion,tameTangentInclusion,originalRealTilt]

end Grad.OriginalCellFamily
