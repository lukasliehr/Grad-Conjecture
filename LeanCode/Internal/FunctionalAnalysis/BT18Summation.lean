import BT17TraceGrade

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryTrace

open Grad.ClosedJets Grad.CartesianState

theorem phaseWeightedJet_boundary_coefficient {dimension : ℕ} (parameters : PhaseParameters)
    (cell mode : ℤ) (field : ClosedJet dimension) :
    fourierCoeff (fun angle : CellCircle =>
      (phaseWeightedJet parameters cell field).value (boundaryDiskPoint angle)) mode =
      Real.exp (boundaryPhase parameters cell) •
        fourierCoeff (fun angle : CellCircle => field.value (boundaryDiskPoint angle)) mode := by
  simp_rw [phaseWeightedJet_value, cartesianWeight_boundary]
  exact fourierCoeff_real_smul _ _ _

def originalBoundaryEnergy {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (field : ACore parameters dimension) (mode : ℤ × ℤ) : ℝ :=
  Real.exp (2 * boundaryPhase parameters mode.2) * boundaryFrequency mode ^ (2 * grade - 1) *
    ‖originalBoundaryCoefficient parameters field mode‖ ^ 2

theorem originalBoundaryEnergy_nonnegative {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (field : ACore parameters dimension) (mode : ℤ × ℤ) :
    0 ≤ originalBoundaryEnergy parameters grade field mode := by
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le
    (pow_nonneg (boundaryFrequency_pos _).le _)) (sq_nonneg _)

theorem finite_original_boundary_cell {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (gradePositive : 1 ≤ grade) (field : ACore parameters dimension)
    (cell : ℤ) (modes : Finset ℤ) :
    (∑ mode ∈ modes, originalBoundaryEnergy parameters grade field (mode, cell)) ≤
      traceCellConstant grade * ‖cellGradeRowLinear (grade := grade) parameters cell (field.1 cell)‖ ^ 2 := by
  have bound := finite_trace_original_cell parameters cell grade gradePositive (field.1 cell) modes
  apply le_trans (le_of_eq ?_) bound
  apply Finset.sum_congr rfl
  intro mode _
  rw [phaseWeightedJet_boundary_coefficient, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow]
  unfold originalBoundaryEnergy originalBoundaryCoefficient
  simp only [two_mul, Real.exp_add, pow_two]
  ring

theorem original_rows_summable {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) :
    Summable (fun cell : ℤ => ‖cellGradeRowLinear (grade := grade) parameters cell (field.1 cell)‖ ^ 2) :=
  (memlp_iff_summable_sq _).mp (field.property grade)

theorem originalGrade_norm_sq_eq_rows {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) :
    ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2 =
      ∑' cell : ℤ, ‖cellGradeRowLinear (grade := grade) parameters cell (field.1 cell)‖ ^ 2 := by
  rw [gradeCore_norm_eq_cartesianGradeSeminorm, cartesianGradeSeminorm_apply]
  have identity := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (cartesianGradeCoordinates parameters grade field)
  norm_num at identity
  exact identity

theorem finite_original_boundary_bound {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (gradePositive : 1 ≤ grade) (field : ACore parameters dimension)
    (modes : Finset (ℤ × ℤ)) :
    (∑ mode ∈ modes, originalBoundaryEnergy parameters grade field mode) ≤
      traceCellConstant grade * ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2 := by
  classical
  have rectangular : modes ⊆ modes.image Prod.fst ×ˢ modes.image Prod.snd := by
    intro mode member
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨mode, member, rfl⟩,
      Finset.mem_image.mpr ⟨mode, member, rfl⟩⟩
  calc
    _ ≤ ∑ mode ∈ modes.image Prod.fst ×ˢ modes.image Prod.snd,
        originalBoundaryEnergy parameters grade field mode :=
      Finset.sum_le_sum_of_subset_of_nonneg rectangular
        (fun mode _ _ => originalBoundaryEnergy_nonnegative parameters grade field mode)
    _ = ∑ cell ∈ modes.image Prod.snd, ∑ mode ∈ modes.image Prod.fst,
        originalBoundaryEnergy parameters grade field (mode, cell) := by
      rw [Finset.sum_product, Finset.sum_comm]
    _ ≤ ∑ cell ∈ modes.image Prod.snd,
        traceCellConstant grade * ‖cellGradeRowLinear (grade := grade) parameters cell (field.1 cell)‖ ^ 2 :=
      Finset.sum_le_sum (fun cell _ => finite_original_boundary_cell parameters grade gradePositive field cell _)
    _ = traceCellConstant grade * (∑ cell ∈ modes.image Prod.snd,
        ‖cellGradeRowLinear (grade := grade) parameters cell (field.1 cell)‖ ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ traceCellConstant grade * (∑' cell : ℤ,
        ‖cellGradeRowLinear (grade := grade) parameters cell (field.1 cell)‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        ((original_rows_summable parameters field).sum_le_tsum _ (fun _ _ => sq_nonneg _))
        (traceCellConstant_nonnegative grade)
    _ = _ := by rw [originalGrade_norm_sq_eq_rows]

theorem original_boundary_summable {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (gradePositive : 1 ≤ grade) (field : ACore parameters dimension) :
    Summable (originalBoundaryEnergy parameters grade field) :=
  summable_of_sum_le (originalBoundaryEnergy_nonnegative parameters grade field)
    (finite_original_boundary_bound parameters grade gradePositive field)

theorem original_boundary_bound {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (gradePositive : 1 ≤ grade) (field : ACore parameters dimension) :
    (∑' mode : ℤ × ℤ, originalBoundaryEnergy parameters grade field mode) ≤
      traceCellConstant grade * ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2 := by
  exact Real.tsum_le_of_sum_le (originalBoundaryEnergy_nonnegative parameters grade field)
    (finite_original_boundary_bound parameters grade gradePositive field)

end Grad.BoundaryTrace
