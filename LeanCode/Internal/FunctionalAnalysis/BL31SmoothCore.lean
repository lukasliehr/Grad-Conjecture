import BL30Compatibility

noncomputable section

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints
  Grad.CompatibleCompletion

def positiveLiftCore {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) :
    BoundaryCore parameters dimension →ₗ[ℂ] AGrade parameters dimension grade :=
  (completedBoundaryLift parameters grade gradePositive).toLinearMap.comp
    (boundaryToGrade parameters grade gradePositive)

def liftGradeFamily {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ) :
    BoundaryCore parameters dimension →ₗ[ℂ] AGrade parameters dimension grade :=
  match grade with
  | 0 => (completedInclusion parameters (by omega : 0 ≤ 1)).toLinearMap.comp
      (positiveLiftCore parameters 1 (by omega))
  | grade + 1 => positiveLiftCore parameters (grade + 1) (by omega)

theorem liftGradeFamily_positive {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (values : BoundaryCore parameters dimension) :
    liftGradeFamily parameters grade values =
      completedBoundaryLift parameters grade gradePositive
        (boundaryToGrade parameters grade gradePositive values) := by
  cases grade with
  | zero => omega
  | succ grade => rfl

theorem liftGradeFamily_compatible {dimension : ℕ} (parameters : PhaseParameters)
    (values : BoundaryCore parameters dimension) (lower upper : ℕ) (ordered : lower ≤ upper) :
    completedInclusion parameters ordered (liftGradeFamily parameters upper values) =
      liftGradeFamily parameters lower values := by
  cases lower with
  | zero =>
    cases upper with
    | zero => rw [completedInclusion_self]; rfl
    | succ upper =>
      have relation := completedBoundaryLift_core_compatible parameters
        (by omega : 1 ≤ upper + 1) (by omega : 1 ≤ 1) values
      have composition := DFunLike.congr_fun (completedInclusion_comp (dimension := dimension)
        parameters (by omega : 1 ≤ upper + 1) (by omega : 0 ≤ 1))
        (liftGradeFamily parameters (upper + 1) values)
      rw [← composition]
      change completedInclusion parameters (by omega : 0 ≤ 1)
        (completedInclusion parameters (by omega : 1 ≤ upper + 1)
          (completedBoundaryLift parameters (upper + 1) (by omega)
            (boundaryToGrade parameters (upper + 1) (by omega) values))) = _
      rw [relation]
      rfl
  | succ lower =>
    rw [liftGradeFamily_positive parameters upper (by omega),
      liftGradeFamily_positive parameters (lower + 1) (by omega)]
    exact completedBoundaryLift_core_compatible parameters ordered (by omega) values

def boundaryLiftCompatible {dimension : ℕ} (parameters : PhaseParameters) :
    BoundaryCore parameters dimension →ₗ[ℂ] CompatibleAGrades parameters dimension where
  toFun values := ⟨fun grade => liftGradeFamily parameters grade values,
    liftGradeFamily_compatible parameters values⟩
  map_add' first second := by
    apply Subtype.ext
    funext grade
    exact (liftGradeFamily parameters grade).map_add first second
  map_smul' scalar values := by
    apply Subtype.ext
    funext grade
    exact (liftGradeFamily parameters grade).map_smul scalar values

/-- One original smooth-core lift, chosen before the grade. Grade zero is
the canonical inclusion of grade one, not a fictitious boundary L2 input. -/
def boundaryLift {dimension : ℕ} (parameters : PhaseParameters) :
    BoundaryCore parameters dimension →ₗ[ℂ] ACore parameters dimension :=
  (compatibleToCore parameters).comp (boundaryLiftCompatible parameters)

theorem boundaryLift_component {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (values : BoundaryCore parameters dimension) :
    aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) (boundaryLift parameters values)) =
      completedBoundaryLift parameters grade gradePositive
        (boundaryToGrade parameters grade gradePositive values) := by
  change aGradeEta parameters (GradeCore.ofCoreLinear
    (compatibleToCore parameters (boundaryLiftCompatible parameters values))) = _
  rw [compatibleToCore_component]
  exact liftGradeFamily_positive parameters grade gradePositive values

theorem boundaryLift_norm_le {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (values : BoundaryCore parameters dimension) :
    ‖GradeCore.ofCoreLinear (grade := grade) (boundaryLift parameters values)‖ ≤
      Real.sqrt (originalLiftCellConstant parameters grade) *
        ‖boundaryToGrade parameters grade gradePositive values‖ := by
  rw [← aGradeEta_norm parameters, boundaryLift_component parameters grade gradePositive]
  exact ((completedBoundaryLift parameters grade gradePositive).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (completedBoundaryLift_norm_le parameters grade gradePositive) (norm_nonneg _))

theorem boundaryLift_coefficient {dimension : ℕ} (parameters : PhaseParameters)
    (values : BoundaryCore parameters dimension) (mode : ℤ × ℤ) :
    originalBoundaryCoefficient parameters (boundaryLift parameters values) mode = values.1 mode := by
  change originalBoundaryCoefficient parameters
    (GradeCore.ofCoreLinear (grade := 1) (boundaryLift parameters values)).toCore mode = _
  rw [← completedTrace_coefficient parameters 1 (by omega)
    (GradeCore.ofCoreLinear (boundaryLift parameters values)) mode,
    boundaryLift_component parameters 1 (by omega), completedBoundaryLift_trace_apply,
    boundaryToGrade_coefficient]

theorem boundaryLift_finite {dimension : ℕ} (parameters : PhaseParameters)
    (values : FiniteBoundaryData dimension) :
    boundaryLift parameters (finiteBoundaryCoreLinear parameters dimension values) =
      finiteLiftLinear parameters dimension values := by
  have equality := boundaryLift_component parameters 1 (by omega)
    (finiteBoundaryCoreLinear parameters dimension values)
  change aGradeEta parameters (GradeCore.ofCoreLinear (grade := 1)
    (boundaryLift parameters (finiteBoundaryCoreLinear parameters dimension values))) =
      completedBoundaryLift parameters 1 (by omega)
        (finiteBoundaryToGrade parameters 1 (by omega) values) at equality
  rw [completedBoundaryLift_finite] at equality
  exact congrArg GradeCore.toCore (aGradeEta_injective parameters equality)

end Grad.BoundaryLift
