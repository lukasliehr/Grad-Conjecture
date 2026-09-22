import RadialLiteralConsumer
import FP17DerivativeShift

noncomputable section

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct

def partialCoefficient {dimension : ℕ} (direction : Fin 2)
    (field : ClosedJet dimension) : C(ClosedDisk, ComplexEuclidean dimension) :=
  closedDerivative field 1 (fun _ => direction)

def laplacianCoefficient {dimension : ℕ} (field : ClosedJet dimension) :
    C(ClosedDisk, ComplexEuclidean dimension) :=
  closedDerivative field 2 (fun _ => 0) + closedDerivative field 2 (fun _ => 1)

def IsActualPartial {dimension : ℕ} {parameters : PhaseParameters}
    (direction : Fin 2) (field output : ACore parameters dimension) : Prop :=
  ∀ cell, (output.val cell).value = partialCoefficient direction (field.val cell)

def IsActualLaplacian {dimension : ℕ} {parameters : PhaseParameters}
    (field output : ACore parameters dimension) : Prop :=
  ∀ cell, (output.val cell).value = laplacianCoefficient (field.val cell)

/-- O1 at the unchanged original width. The actual all-grade map and its
one-grade estimate are conclusions; dimension, cell and phase parameters
do not enter the numerical constants. -/
def CartesianDerivativeGoal : Prop :=
  ∃ constants : ℕ → ℝ, (∀ grade, 0 ≤ constants grade) ∧
    ∀ (parameters : PhaseParameters) (dimension : ℕ) (direction : Fin 2),
      ∃ mapping : ACore parameters dimension →ₗ[ℂ] ACore parameters dimension,
        (∀ field, IsActualPartial direction field (mapping field)) ∧
        ∀ grade field, originalGradeNorm grade (mapping field) ≤
          constants grade * originalGradeNorm (grade + 1) field

/-- The literal coefficientwise i*n time derivative, with constant one. -/
def TimeDerivativeGoal : Prop :=
  ∀ (parameters : PhaseParameters) (dimension : ℕ),
    ∃ mapping : ACore parameters dimension →ₗ[ℂ] ACore parameters dimension,
      (∀ field cell, (mapping field).val cell =
        ((cell : ℂ) * Complex.I) • field.val cell) ∧
      ∀ grade field, originalGradeNorm grade (mapping field) ≤
        originalGradeNorm (grade + 1) field

def LaplacianGoal : Prop :=
  ∃ constants : ℕ → ℝ, (∀ grade, 0 ≤ constants grade) ∧
    ∀ (parameters : PhaseParameters) (dimension : ℕ),
      ∃ mapping : ACore parameters dimension →ₗ[ℂ] ACore parameters dimension,
        (∀ field, IsActualLaplacian field (mapping field)) ∧
        ∀ grade field, originalGradeNorm grade (mapping field) ≤
          constants grade * originalGradeNorm (grade + 2) field

/-- Genuine original AGrade completion, retaining the same literal core
map at every grade and the exact dense-core embedding law. -/
def CartesianDerivativeCompletedGoal : Prop :=
  ∃ constants : ℕ → ℝ, (∀ grade, 0 ≤ constants grade) ∧
    ∀ (parameters : PhaseParameters) (dimension : ℕ) (direction : Fin 2),
      ∃ core : ACore parameters dimension →ₗ[ℂ] ACore parameters dimension,
        (∀ field, IsActualPartial direction field (core field)) ∧
        ∀ grade, ∃ completed : AGrade parameters dimension (grade + 1) →L[ℂ]
            AGrade parameters dimension grade,
          (∀ field : ACore parameters dimension,
            completed (aGradeEta parameters (GradeCore.ofCoreLinear field)) =
              aGradeEta parameters (GradeCore.ofCoreLinear (core field))) ∧
          ∀ field, ‖completed field‖ ≤ constants grade * ‖field‖

end Grad.NonlinearQuotientBounds
