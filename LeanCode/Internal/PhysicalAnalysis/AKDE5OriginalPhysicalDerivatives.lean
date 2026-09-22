import AKDE3OriginalChartValues
import AKCH2OriginalProductDirections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 3500
open Set Filter
open scoped ContDiff Topology

namespace Grad.OriginalCellFamily
open Grad.CartesianState Grad.ClosedJets Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.OriginalParameterEvaluation Grad.OriginalCoreRealization Grad.DiskExtension.Operator

variable {dimension : ℕ} {parameters : PhaseParameters}

def originalProductField (field : ACore parameters dimension) : SpatialPlane × ℝ → ComplexEuclidean dimension :=
  fun point => originalExtendedField parameters field (assembleSpatialCell point.1 point.2)

theorem originalProductField_smooth (field : ACore parameters dimension) :
    ContDiff ℝ ∞ (originalProductField field) :=
  (originalExtendedField_smooth parameters field).comp assembleSpatialCellCLM.contDiff

theorem originalProductField_same_fderiv (field : ACore parameters dimension)
    (point : SpatialPlane × ℝ) (inside : ‖point.1‖ < 1) :
    fderiv ℝ (originalProductField field) point = fderiv ℝ (originalCoreProductLift parameters field) point := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [((isOpen_lt continuous_norm continuous_const).prod isOpen_univ).mem_nhds
    (show point ∈ {point : SpatialPlane | ‖point‖ < 1} ×ˢ (univ : Set ℝ) from ⟨inside,mem_univ _⟩)] with query member
  have queryInside : ‖query.1‖ < 1 := member.1
  rw [originalCoreProductLift_value parameters field query queryInside]
  exact originalExtendedField_coreValue field ⟨query.1,queryInside.le⟩ query.2

private theorem originalProductField_closed_derivative (field derivative : ACore parameters dimension)
    (direction : SpatialPlane × ℝ)
    (interior : ∀ point : SpatialPlane × ℝ, ‖point.1‖ < 1 →
      fderiv ℝ (originalProductField field) point direction = originalProductField derivative point)
    (point : ClosedDisk) (cell : ℝ) :
    fderiv ℝ (originalProductField field) (point.val,cell) direction =
      originalProductField derivative (point.val,cell) := by
  let first : ContinuousMap ClosedDisk (ComplexEuclidean dimension) :=
    ⟨fun point => fderiv ℝ (originalProductField field) (point.val,cell) direction,
      (((originalProductField_smooth field).continuous_fderiv (by simp)).comp
        (continuous_subtype_val.prodMk continuous_const)).clm_apply continuous_const⟩
  let second : ContinuousMap ClosedDisk (ComplexEuclidean dimension) :=
    ⟨fun point => originalProductField derivative (point.val,cell),
      (originalProductField_smooth derivative).continuous.comp (continuous_subtype_val.prodMk continuous_const)⟩
  have equal := continuousMap_eq_of_openDisk first second (fun point member => interior (point.val,cell) member)
  exact congrArg (fun function : ContinuousMap ClosedDisk (ComplexEuclidean dimension) => function point) equal

/-- The true P09 derivative agrees with the original partial core, including
both the axis and the outer circle. -/
theorem originalProductField_partial (field : ACore parameters dimension)
    (point : ClosedDisk) (cell : ℝ) (direction : Fin 2) :
    fderiv ℝ (originalProductField field) (point.val,cell) (spatialBasis direction,0) =
      originalProductField (partialCore parameters direction field) (point.val,cell) := by
  apply originalProductField_closed_derivative
  intro query inside
  rw [originalProductField_same_fderiv field query inside,originalCoreProductLift_partial parameters field query inside]
  exact (originalExtendedField_coreValue (partialCore parameters direction field) ⟨query.1,inside.le⟩ query.2).symm

/-- The true P09 cell derivative is the original time-derivative core on the
whole closed disk, with its original period. -/
theorem originalProductField_axial (field : ACore parameters dimension)
    (point : ClosedDisk) (cell : ℝ) :
    fderiv ℝ (originalProductField field) (point.val,cell) (0,1) =
      originalProductField (timeDerivativeCore parameters field) (point.val,cell) := by
  apply originalProductField_closed_derivative
  intro query inside
  rw [originalProductField_same_fderiv field query inside,originalCoreProductLift_axial parameters field query inside]
  exact (originalExtendedField_coreValue (timeDerivativeCore parameters field) ⟨query.1,inside.le⟩ query.2).symm

end Grad.OriginalCellFamily
