import BTProof

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryTrace.Consumer

open Grad.ClosedJets Grad.CartesianState

theorem original_half_order_trace {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (field : ACore parameters dimension) :
    (∑' mode : ℤ × ℤ, Real.exp (2 * boundaryPhase parameters mode.2) *
      (Real.sqrt (1 + (mode.1 : ℝ) ^ 2 + (mode.2 : ℝ) ^ 2)) ^ (2 * grade - 1) *
      ‖fourierCoeff (fun angle : CellCircle => (field.1 mode.2).value (boundaryDiskPoint angle)) mode.1‖ ^ 2) ≤
      traceCellConstant grade * ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2 :=
  original_boundary_bound parameters grade gradePositive field

theorem completed_original_half_order_trace {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (field : AGrade parameters dimension grade) :
    (∑' mode : ℤ × ℤ, Real.exp (2 * boundaryPhase parameters mode.2) *
      (Real.sqrt (1 + (mode.1 : ℝ) ^ 2 + (mode.2 : ℝ) ^ 2)) ^ (2 * grade - 1) *
      ‖boundaryCoefficient parameters grade (completedTrace parameters grade gradePositive field) mode‖ ^ 2) ≤
      traceCellConstant grade * ‖field‖ ^ 2 :=
  completedTrace_weighted_bound parameters grade gradePositive field

/-- The output coefficient is original h; applying W_gamma at the boundary multiplies it by exp Phi_n(1). -/
theorem actual_weighted_double_fourier_consumer {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (gradePositive : 1 ≤ grade) (field : ACore parameters dimension) (mode : ℤ × ℤ) :
    weightedBoundaryCoefficient parameters field mode = Real.exp (boundaryPhase parameters mode.2) •
      boundaryCoefficient parameters grade
        (completedTrace parameters grade gradePositive
          (aGradeEta parameters (GradeCore.ofCoreLinear field))) mode := by
  rw [completedTrace_coefficient, weightedBoundaryCoefficient_original]
  rfl

theorem trace_output_is_hilbert {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ) :
    CompleteSpace (BoundaryGrade parameters (ComplexEuclidean dimension) grade) := inferInstance

end Grad.BoundaryTrace.Consumer
