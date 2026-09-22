import SBT2IntegerTrace
import QuotientVectorDerivatives
import QuotientValueMap
import AXF20VectorNorm

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.SourceBoundaryTrace
open Grad.SourceCollarDivision Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace
open Grad.NonlinearQuotientBounds Grad.FlatSourceProjection
open Grad.NonlinearProduct
open Grad.Constraints (valueMapJet valueMapJet_value)

/-- Smooth Cartesian extension Jy dot f; it equals e_theta dot f only on
the unit boundary. No radius division or false interior identity is used. -/
def tangentialBoundaryCore (parameters : PhaseParameters) :
    ACore parameters 2 →ₗ[ℂ] ACore parameters 1 :=
  (coordinateCore parameters 0).comp (valueMapCore parameters (componentValue 2 1)) -
    (coordinateCore parameters 1).comp (valueMapCore parameters (componentValue 2 0))

def tangentialBoundaryConstant (grade : ℕ) : ℝ :=
  coordinateGradeConstant grade * (‖componentValue 2 1‖ + ‖componentValue 2 0‖)

theorem tangentialBoundaryConstant_nonnegative (grade : ℕ) : 0 ≤ tangentialBoundaryConstant grade :=
  mul_nonneg (coordinateGradeConstant_nonnegative _) (add_nonneg (norm_nonneg _) (norm_nonneg _))

theorem tangentialBoundaryCore_bound (parameters : PhaseParameters) (grade : ℕ) (field : ACore parameters 2) :
    originalGradeNorm grade (tangentialBoundaryCore parameters field) ≤
      tangentialBoundaryConstant grade * originalGradeNorm grade field := by
  apply (originalGradeNorm_sub_le grade _ _).trans
  have first := (coordinateCore_bound parameters 0 _ grade).trans
    (mul_le_mul_of_nonneg_left (valueMapCore_bound (componentValue 2 1) field grade)
      (coordinateGradeConstant_nonnegative _))
  have second := (coordinateCore_bound parameters 1 _ grade).trans
    (mul_le_mul_of_nonneg_left (valueMapCore_bound (componentValue 2 0) field grade)
      (coordinateGradeConstant_nonnegative _))
  exact (add_le_add first second).trans_eq (by unfold tangentialBoundaryConstant; ring)

theorem tangentialBoundaryCore_value (parameters : PhaseParameters)
    (field : ACore parameters 2) (cell : ℤ) (point : ClosedDisk) :
    ((tangentialBoundaryCore parameters field).val cell).value point 0 =
      (point.val 0 : ℂ) * (field.val cell).value point 1 -
        (point.val 1 : ℂ) * (field.val cell).value point 0 := by
  change ((coordinateJet 0 (valueMapJet (componentValue 2 1) (field.val cell)) +
    -(coordinateJet 1 (valueMapJet (componentValue 2 0) (field.val cell)))).value point) 0 = _
  rw [closedJet_value_add, closedJet_value_neg]
  simp [coordinateJet_value, valueMapJet_value, componentValue, Complex.real_smul,
    sub_eq_add_neg]

/-- This is the literal physical F0 at r=1, with the original Fourier cells. -/
theorem tangentialBoundaryCore_unit_circle (parameters : PhaseParameters)
    (field : ACore parameters 2) (cell : ℤ) (angle : ℝ) :
    ((tangentialBoundaryCore parameters field).val cell).value (boundaryDiskPoint (angle : CellCircle)) 0 =
      (Real.cos angle : ℂ) * (field.val cell).value (boundaryDiskPoint (angle : CellCircle)) 1 -
        (Real.sin angle : ℂ) * (field.val cell).value (boundaryDiskPoint (angle : CellCircle)) 0 := by
  rw [tangentialBoundaryCore_value]
  simp only [boundaryDiskPoint, boundaryCirclePoint_coe, collarPlane, sub_zero, one_mul,
    WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one]

def tangentialBoundaryCompleted (parameters : PhaseParameters) (grade : ℕ) :
    AGrade parameters 2 grade →L[ℂ] AGrade parameters 1 grade :=
  denseCoreExtension parameters
    ((aGradeEta parameters).toLinearMap.comp
      (GradeCore.ofCoreLinear.comp ((tangentialBoundaryCore parameters).comp GradeCore.toCoreLinear)))
    (tangentialBoundaryConstant grade) (fun field => by
      change ‖aGradeEta parameters (GradeCore.ofCoreLinear (tangentialBoundaryCore parameters field.toCore))‖ ≤ _
      rw [aGradeEta_norm]
      exact tangentialBoundaryCore_bound parameters grade field.toCore)

theorem tangentialBoundaryCompleted_core (parameters : PhaseParameters) (grade : ℕ)
    (field : GradeCore parameters 2 grade) :
    tangentialBoundaryCompleted parameters grade (aGradeEta parameters field) =
      aGradeEta parameters (GradeCore.ofCoreLinear (tangentialBoundaryCore parameters field.toCore)) :=
  denseCoreExtension_apply_eta parameters _ _ _ field

theorem tangentialBoundaryCompleted_bound (parameters : PhaseParameters) (grade : ℕ)
    (field : AGrade parameters 2 grade) :
    ‖tangentialBoundaryCompleted parameters grade field‖ ≤ tangentialBoundaryConstant grade * ‖field‖ :=
  denseCoreExtension_apply_norm_le parameters _ _ _ field

end Grad.SourceBoundaryTrace
