import AXL24LiftLinearity

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.NonlinearProduct Grad.ChartAxisSplit
open Grad.Q24Realization Grad.RealFixedRanges

variable {parameters : PhaseParameters}

def tangentToAxis (parameters : PhaseParameters) : TangentCoefficient parameters →ₗ[ℂ] TCore parameters where
  toFun family := ⟨family.val, fun grade => by
    apply (memlp_iff_summable_sq _).2
    apply (family.property grade).congr
    intro cell
    rw [tangentTerm_eq_axis]
    change _ = ‖Grad.AxisSplit.axisWeight parameters grade cell • family.val cell‖ ^ 2
    rw [norm_smul, Real.norm_of_nonneg (Grad.AxisSplit.axisWeight_pos parameters grade cell).le, mul_pow]
    rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tangentToAxis_norm (grade : ℕ) (family : TangentCoefficient parameters) :
    axisGradeNorm parameters grade (tangentToAxis parameters family) = tangentNorm grade family :=
  (axisToTangent_norm grade (tangentToAxis parameters family)).symm

/-- The actual chart direction extraction, as literal all-grade axis data. -/
def chartKappaData (parameters : PhaseParameters) (direction : Grad.SmoothingFamily.StateCore parameters) :
    AxisData parameters :=
  (⟨scalarOriginGradient direction.2.2, scalarOriginGradient_mem direction.2.2⟩,
    tangentToAxis parameters (smoothingToTangent parameters direction.1))

theorem chartKappaData_coefficients (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (direction : stateSmoothRange parameters reference insideR) :
    ((chartKappaData parameters direction.val).1.val, (chartKappaData parameters direction.val).2.val) =
      chartKappa parameters reference insideR direction := rfl

theorem stateToGrade_literal_norm (grade : ℕ) (direction : Grad.SmoothingFamily.StateCore parameters) :
    ‖Grad.SmoothingFamily.stateToGrade parameters grade direction‖ =
      tangentNorm (grade + 1) (smoothingToTangent parameters direction.1) +
        originalGradeNorm grade direction.2.1 + originalGradeNorm grade direction.2.2 := by
  rw [Grad.AxisCore.stateToGrade_embedded_norm, aGradeEta_norm, aGradeEta_norm,
    ← tangentToGrade_smoothing, tangentToGrade_norm]
  rfl

/-- AL14 in the actual chart carrier, with precisely the three source-grade
shift and the original T^(q+1) axis data sum norm. -/
theorem chartKappaData_bound (grade : ℕ) (direction : Grad.SmoothingFamily.StateCore parameters) :
    axisDataNorm parameters grade (chartKappaData parameters direction) ≤
      (1 + kappaTraceConstant) * ‖Grad.SmoothingFamily.stateToGrade parameters (grade + 3) direction‖ := by
  have scalar := scalarGradient_grade_bound direction.2.2 (grade + 1) (by omega)
  have tangent := axisGradeNorm_mono parameters (show grade + 1 ≤ (grade + 3) + 1 by omega)
    (tangentToAxis parameters (smoothingToTangent parameters direction.1))
  rw [tangentToAxis_norm, tangentToAxis_norm] at tangent
  have gradeEqual : grade + 1 + 2 = grade + 3 := by omega
  rw [gradeEqual] at scalar
  rw [stateToGrade_literal_norm]
  change axisGradeNorm parameters (grade + 1) _ + axisGradeNorm parameters (grade + 1) _ ≤ _
  dsimp only [chartKappaData]
  rw [tangentToAxis_norm]
  have axisNonneg := tangentNorm_nonneg ((grade + 3) + 1) (smoothingToTangent parameters direction.1)
  have vectorNonneg := originalGradeNorm_nonnegative (grade + 3) direction.2.1
  have scalarNonneg := originalGradeNorm_nonnegative (grade + 3) direction.2.2
  nlinarith [mul_nonneg kappaTraceConstant_nonneg axisNonneg,
    mul_nonneg kappaTraceConstant_nonneg vectorNonneg]

end Grad.ChartAxisLift
