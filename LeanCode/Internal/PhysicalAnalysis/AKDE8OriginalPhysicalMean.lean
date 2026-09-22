import AKDE7OriginalExtensionReality
import AXL11AngularFourier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 3500
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace Grad.OriginalCellFamily
open Grad.CartesianState Grad.ClosedJets Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.OriginalParameterEvaluation Grad.OriginalCoreRealization Grad.DiskExtension.Operator
open Grad.PhysicalFamily Grad.Constraints Grad.GaugeCoefficients.Radial

variable {parameters : PhaseParameters}

def originalScalarCell (field : ACore parameters 1) : SpatialPlane → ℝ → ℂ :=
  fun point cell => originalCellField field point cell 0

theorem originalCellField_coreValue {dimension : ℕ} (field : ACore parameters dimension)
    (point : ClosedDisk) (cell : ℝ) :
    originalCellField field point.val cell = coreValue field point cell :=
  originalExtendedField_coreValue field point cell

theorem originalScalarCell_mean (field : ACore parameters 1) (point : ClosedDisk) (cell : ℝ) :
    Grad.NonlinearQuotient.complexAngularAverage (originalScalarCell field) point.val cell =
      originalScalarCell (angularCore parameters 0 field) point.val cell := by
  let projection : ComplexEuclidean 1 →L[ℂ] ℂ := PiLp.proj 2 (fun _ : Fin 1 => ℂ) 0
  have same (angle : ℝ) : originalCellField field (planeRotationAction angle point.val) cell =
      coreValue field (rotatedPoint angle point) cell := by
    rw [physicalRotation_eq_orthogonal]
    exact originalCellField_coreValue field (rotatedPoint angle point) cell
  have continuous : Continuous (fun angle => coreValue field (rotatedPoint angle point) cell) := by
    have rotated := continuous_rotatedPoint_joint.comp (continuous_id.prodMk (continuous_const (y := point)))
    have physical := (originalProductField_smooth field).continuous.comp
      ((continuous_subtype_val.comp rotated).prodMk (continuous_const (y := cell)))
    exact physical.congr (fun angle => originalCellField_coreValue field (rotatedPoint angle point) cell)
  have identity := congrArg projection (Grad.ChartAxisLift.coreValue_angularCore 0 field point cell)
  simp only [angularCharacter_zero_mode,one_smul] at identity
  have scalarLaw := (projection.restrictScalars ℝ).map_smul ((2*Real.pi)⁻¹)
    (∫ angle in (0:ℝ)..2*Real.pi, coreValue field (rotatedPoint angle point) cell)
  change projection (((2*Real.pi)⁻¹ : ℝ) •
      (∫ angle in (0:ℝ)..2*Real.pi, coreValue field (rotatedPoint angle point) cell)) =
    ((2*Real.pi)⁻¹ : ℝ) • projection
      (∫ angle in (0:ℝ)..2*Real.pi, coreValue field (rotatedPoint angle point) cell) at scalarLaw
  rw [scalarLaw,← projection.intervalIntegral_comp_comm (continuous.intervalIntegrable _ _)] at identity
  unfold Grad.NonlinearQuotient.complexAngularAverage originalScalarCell
  rw [originalCellField_coreValue]
  change _ = projection (coreValue (angularCore parameters 0 field) point cell)
  rw [identity]
  congr 1
  apply intervalIntegral.integral_congr
  intro angle _
  exact congrArg projection (same angle)

theorem originalScalarCell_removeMean (field : ACore parameters 1) (point : ClosedDisk) (cell : ℝ) :
    Grad.NonlinearQuotient.complexRemoveAngularAverage (originalScalarCell field) point.val cell =
      originalScalarCell (removeAngularCore parameters field) point.val cell := by
  rw [Grad.NonlinearQuotient.complexRemoveAngularAverage,originalScalarCell_mean]
  change originalCellField field point.val cell 0 - originalCellField (angularCore parameters 0 field) point.val cell 0 =
    originalCellField (field-angularCore parameters 0 field) point.val cell 0
  rw [originalCellField_coreValue,originalCellField_coreValue,originalCellField_coreValue,
    Grad.GaugeCoefficients.Physical.RadialLedger.coreValue_subtract]
  rfl

end Grad.OriginalCellFamily
