import OriginalEvaluationReality

noncomputable section

namespace Grad.CartesianState

open Grad.ClosedJets

local instance originalPublicCellPeriodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Original-coefficient NG_P01 contract.  Recovery is equality of all-order
closed jets with the input `h_n`, not with the phase-multiplied coefficients. -/
def OriginalPhysicalEvaluationGoal : Prop :=
  ∀ (dimension : ℕ) (parameters : PhaseParameters) (j : ℕ),
    ∃ E : ℝ, 0 ≤ E ∧
      (∀ field : GradeCore parameters dimension (j + 3),
        closedPhysicalCNorm (originalPhysicalClosedJet parameters field.toCore) j ≤
          E * ‖field‖) ∧
      (∀ (field : GradeCore parameters dimension (j + 3)) (cell : ℤ),
        diskCellFourierCoefficientJet
          (originalPhysicalClosedJet parameters field.toCore) cell = field.toCore.1 cell) ∧
      (∀ (field : GradeCore parameters dimension (j + 3))
          (point : ClosedDisk) (coordinate : ℝ),
        originalPhysicalEvaluationLift parameters field point coordinate =
          ∑' cell : ℤ, cellExponential cell coordinate • (field.toCore.1 cell).value point) ∧
      (∀ (field : GradeCore parameters dimension (j + 3)),
        GradeCoreReality parameters field →
          ∀ (point : ClosedDisk) (cell : ℝ),
            cartesianPhysicalConjugation dimension
                (originalPhysicalEvaluationLift parameters field point cell) =
              originalPhysicalEvaluationLift parameters field point cell) ∧
      (∀ (field : GradeCore parameters dimension (j + 3))
          (point : ClosedDisk) (cell : ℝ),
        originalPhysicalEvaluationLift parameters field point (cell + 2 * Real.pi) =
          originalPhysicalEvaluationLift parameters field point cell)

theorem originalPhysicalEvaluationBlock : OriginalPhysicalEvaluationGoal := by
  intro dimension parameters j
  exact ⟨originalPhysicalEvaluationConstant parameters j,
    originalPhysicalEvaluationConstant_nonnegative parameters j,
    originalField_closedPhysicalCNorm_bound parameters,
    fun field cell => originalPhysicalClosedJet_fourierCoefficient parameters field.toCore cell,
    originalPhysicalEvaluationLift_eq_tsum parameters,
    originalPhysicalEvaluationLift_real parameters,
    originalPhysicalEvaluationLift_periodic parameters⟩

end Grad.CartesianState
