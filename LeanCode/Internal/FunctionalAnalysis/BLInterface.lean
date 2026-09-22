import BL1BoundaryCore
import OriginalCoefficientCore
import FiniteAngularProjection
import MultiplierInterface

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

/-- Fixed original parameters already contain 0 < gamma < min(1,sigma0).
The lift is one smooth-core operator at all grades, with the literal kernel,
and a same-grade extension on each positive half-order completion. -/
def BoundaryLiftGoal : Prop :=
  ∀ parameters : PhaseParameters, ∃ constants : ℕ → ℝ,
    (∀ grade, 0 ≤ constants grade) ∧
    ∀ dimension : ℕ, ∃ lift : BoundaryCore parameters dimension →ₗ[ℂ] ACore parameters dimension,
      (∀ grade (gradePositive : 1 ≤ grade) (values : BoundaryCore parameters dimension),
        ‖GradeCore.ofCoreLinear (grade := grade) (lift values)‖ ≤
          constants grade * ‖boundaryToGrade parameters grade gradePositive values‖) ∧
      (∀ values : BoundaryCore parameters dimension, ∀ mode : ℤ × ℤ,
        originalBoundaryCoefficient parameters (lift values) mode = values.1 mode) ∧
      (∀ values : BoundaryCore parameters dimension, ∀ point : ClosedDisk,
        ‖point.val‖ ≤ (3 / 4 : ℝ) → ∀ cell : ℤ, ((lift values).1 cell).value point = 0) ∧
      (∀ values : BoundaryCore parameters dimension, ∀ point : ClosedDisk,
        ∀ time : ℝ, 0 ≤ time → time ≤ (1 / 4 : ℝ) → ∀ angle cell : CellCircle,
          point.val = (1 - time) • boundaryCirclePoint angle →
          (originalPhysicalClosedJet parameters (lift values)).value (point, cell) =
            literalBoundaryLift values.1 time angle cell) ∧
      (∀ values : BoundaryCore parameters dimension, BoundaryReality parameters values →
        ∀ cell : ℤ, (lift values).1 (-cell) = closedJetConjugate ((lift values).1 cell)) ∧
      (∀ values : BoundaryCore parameters dimension, HighBoundarySupport parameters values →
        ∀ mode : ℤ, |mode| ≤ 2 → ∀ cell : ℤ, angularClosedJet mode ((lift values).1 cell) = 0) ∧
      (∀ grade (gradePositive : 1 ≤ grade),
        ∃ completed : BoundaryGrade parameters (ComplexEuclidean dimension) grade →L[ℂ]
            AGrade parameters dimension grade,
          ‖completed‖ ≤ constants grade ∧
          (completedTrace parameters grade gradePositive).comp completed = ContinuousLinearMap.id ℂ _ ∧
          ∀ values : BoundaryCore parameters dimension,
            completed (boundaryToGrade parameters grade gradePositive values) =
              aGradeEta parameters (GradeCore.ofCoreLinear (lift values)))

/-- N28 on its actual fixed half-order completed target and literal N6 envelope. -/
def BoundaryMultiplicationGoal : Prop :=
  ∀ (grade : ℕ), 1 ≤ grade → ∀ (parameters : PhaseParameters),
    ∀ (sourceDimension targetDimension : ℕ)
      (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension),
      Summable (Grad.Constraints.Multipliers.envelopeTerm parameters grade coefficients) →
      ∃ mapping : BoundaryGrade parameters (ComplexEuclidean sourceDimension) grade →L[ℂ]
          BoundaryGrade parameters (ComplexEuclidean targetDimension) grade,
        ‖mapping‖ ≤ Grad.Constraints.Multipliers.envelope parameters grade coefficients ∧
        ∀ field : BoundaryGrade parameters (ComplexEuclidean sourceDimension) grade,
          ∀ mode : ℤ × ℤ,
            HasSum (fun shift : ℤ => coefficients shift
              (boundaryCoefficient parameters grade field (mode.1, mode.2 - shift)))
              (boundaryCoefficient parameters grade (mapping field) mode)

def BoundaryAngularOperationsGoal : Prop :=
  ∀ (grade : ℕ), 1 ≤ grade → ∀ (parameters : PhaseParameters) (dimension : ℕ),
    (∀ shift : ℤ, ∃ mapping : BoundaryGrade parameters (ComplexEuclidean dimension) grade →L[ℂ]
        BoundaryGrade parameters (ComplexEuclidean dimension) grade,
      ‖mapping‖ ≤ (1 + |(shift : ℝ)|) ^ grade ∧
      ∀ field mode, boundaryCoefficient parameters grade (mapping field) mode =
        boundaryCoefficient parameters grade field (mode.1 - shift, mode.2)) ∧
    (∃ projection : BoundaryGrade parameters (ComplexEuclidean dimension) grade →L[ℂ]
        BoundaryGrade parameters (ComplexEuclidean dimension) grade,
      ‖projection‖ ≤ 1 ∧ projection.comp projection = projection ∧
      ∀ field mode, boundaryCoefficient parameters grade (projection field) mode =
        if |mode.1| ≤ 2 then 0 else boundaryCoefficient parameters grade field mode)

def BlockGoal : Prop := BoundaryLiftGoal ∧ BoundaryMultiplicationGoal ∧ BoundaryAngularOperationsGoal

end Grad.BoundaryLift
