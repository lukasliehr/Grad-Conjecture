import SBT8OuterTuple
import SC8PublicBoundary

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.SourceBoundaryTrace
open Grad.ClosedJets Grad.CartesianState Grad.AxisCore Grad.QuotientProjection
open Grad.FlatSourceProjection Grad.NonlinearProduct Grad.NonlinearQuotientBounds
open Grad.BoundaryTrace Grad.CompatibleCompletion Grad.NonlinearRange Grad.SourceCollar

theorem polarClosedPoint_one (angle : ℝ) :
    Grad.Constraints.polarClosedPoint 1 (by norm_num) angle = boundaryDiskPoint (angle : CellCircle) := by
  apply Subtype.ext
  rw [Grad.Constraints.polarClosedPoint_coordinates]
  change WithLp.toLp 2 ![1 * Real.cos angle, 1 * Real.sin angle] = boundaryCirclePoint (angle : CellCircle)
  rw [boundaryCirclePoint_coe]
  simp [collarPlane]

theorem coreValue_coordinate_original {dimension : ℕ} (parameters : PhaseParameters)
    (coordinate : Fin 2) (field : ACore parameters dimension) (point : ClosedDisk) (angle : ℝ) :
    coreValue (coordinateCore parameters coordinate field) point angle =
      point.val coordinate • coreValue field point angle := by
  unfold coreValue
  simp_rw [coordinateCore_actual, smul_comm (axialPhase _ angle) (point.val coordinate)]
  exact tsum_const_smul'' (point.val coordinate)

theorem tangentialBoundaryCore_physical (parameters : PhaseParameters)
    (field : ACore parameters 2) (point : ClosedDisk) (angle : ℝ) :
    coreValue (tangentialBoundaryCore parameters field) point angle 0 =
      (point.val 0 : ℂ) * coreValue field point angle 1 -
        (point.val 1 : ℂ) * coreValue field point angle 0 := by
  change coreValue (coordinateCore parameters 0 (valueMapCore parameters (componentValue 2 1) field) -
    coordinateCore parameters 1 (valueMapCore parameters (componentValue 2 0) field)) point angle 0 = _
  rw [sub_eq_add_neg, ← neg_one_smul ℂ (coordinateCore parameters 1 _), coreValue_add, coreValue_smul,
    coreValue_coordinate_original, coreValue_coordinate_original, coreValue_valueMap, coreValue_valueMap]
  simp [componentValue, Complex.real_smul, sub_eq_add_neg]

/-- The same original physical point as the repaired BS30 conversion.
The polynomial extension is used only at r=1. -/
theorem sourceForce_physical_outer (parameters : PhaseParameters) (L epsilon : ℝ)
    (state : ACore parameters 3) (source : CartesianSourceCore parameters)
    (axialAngle polarAngle : ℝ) :
    coreValue (tangentialBoundaryCore parameters source.1)
      (boundaryDiskPoint (polarAngle : CellCircle)) axialAngle 0 =
      (actualAnnularBulkSource parameters L epsilon state 1 (by norm_num) axialAngle source).F0 polarAngle := by
  rw [tangentialBoundaryCore_physical]
  change _ = Grad.Constraints.polarTangentialComponent polarAngle
    (coreValue source.1 (Grad.Constraints.polarClosedPoint 1 (by norm_num) polarAngle) axialAngle)
  rw [polarClosedPoint_one]
  simp only [boundaryDiskPoint, boundaryCirclePoint_coe, collarPlane, sub_zero, one_mul,
    WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Grad.Constraints.polarTangentialComponent]
  ring

theorem sourceFourth_physical_outer (parameters : PhaseParameters) (L epsilon : ℝ)
    (state : ACore parameters 3) (source : CartesianSourceCore parameters)
    (axialAngle polarAngle : ℝ) :
    (L : ℂ)⁻¹ * coreValue source.2.2 (boundaryDiskPoint (polarAngle : CellCircle)) axialAngle 0 =
      (actualAnnularBulkSource parameters L epsilon state 1 (by norm_num) axialAngle source).F2 polarAngle := by
  change _ = coreValue source.2.2 (Grad.Constraints.polarClosedPoint 1 (by norm_num) polarAngle) axialAngle 0 / (L : ℂ)
  rw [polarClosedPoint_one, div_eq_mul_inv, mul_comm]

theorem sourceOuterTrace_cartesian_bound (parameters : PhaseParameters) (L : ℝ) (positive : 0 < L)
    (power : ℕ) (source : CartesianSourceCore parameters) :
    ‖sourceOuterTrace parameters L power
      (quotientEta parameters (power + 2) (cartesianToSpin source))‖ ≤
        sourceOuterTraceConstant L power * cartesianSourceNorm (power + 2) source := by
  have bound := sourceOuterTrace_bound parameters L positive power
    (quotientEta parameters (power + 2) (cartesianToSpin source))
  change _ ≤ sourceOuterTraceConstant L power * quotientNorm parameters (power + 2) (cartesianToSpin source) at bound
  rwa [cartesianToSpin_norm] at bound

end Grad.SourceBoundaryTrace
