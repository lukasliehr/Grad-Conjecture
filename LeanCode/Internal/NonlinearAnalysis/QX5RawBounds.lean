import QX4RawDeterminant

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

open Filter
open scoped BigOperators Topology

namespace Grad.RawForward

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.NonlinearProduct Grad.QuotientProjection Grad.AxisSplit

variable {parameters : PhaseParameters}

/-- A same-grade bound for spatial multiplication in the reconstruction.
This auxiliary row-sum estimate does not change the original quotient norm. -/
theorem rawReconstructionCore_rows_bound (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ rows : QuotientRows parameters,
      rowsGradeNorm grade (rawReconstructionCore parameters rows) ≤
        constant * rowsGradeNorm grade rows := by
  let coordinate := 2 * coordinateGradeConstant grade
  have nonnegative : 0 ≤ coordinate := mul_nonneg (by norm_num) (coordinateGradeConstant_nonnegative grade)
  let weights : Fin 4 → ℝ :=
    ![‖(2 * Complex.I)⁻¹‖ * (2 * coordinate), ‖(1 / 2 : ℂ)‖ * (2 * coordinate), 1,
      coordinate * coordinate]
  refine ⟨∑ index, weights index, ?_, ?_⟩
  · apply Finset.sum_nonneg
    intro index _
    fin_cases index
    · exact mul_nonneg (norm_nonneg _) (mul_nonneg (by norm_num) nonnegative)
    · exact mul_nonneg (norm_nonneg _) (mul_nonneg (by norm_num) nonnegative)
    · exact zero_le_one
    · exact mul_nonneg nonnegative nonnegative
  · intro rows
    let total := rowsGradeNorm grade rows
    have component (index : Fin 4) : originalGradeNorm grade (rows index) ≤ total :=
      Finset.single_le_sum (fun _ _ => originalGradeNorm_nonnegative _ _) (Finset.mem_univ index)
    have zBound (index : Fin 4) : originalGradeNorm grade (zMulCore parameters (rows index)) ≤ coordinate * total :=
      (zMulCore_bound (rows index) grade).trans
        (mul_le_mul_of_nonneg_left (component index) nonnegative)
    have starBound (index : Fin 4) : originalGradeNorm grade (starZMulCore parameters (rows index)) ≤ coordinate * total :=
      (starZMulCore_bound (rows index) grade).trans
        (mul_le_mul_of_nonneg_left (component index) nonnegative)
    have pairSub : originalGradeNorm grade (starZMulCore parameters (rows 0) - zMulCore parameters (rows 1)) ≤
        (2 * coordinate) * total :=
      (originalGradeNorm_sub_le grade _ _).trans
        ((add_le_add (starBound 0) (zBound 1)).trans_eq (by ring))
    have pairAdd : originalGradeNorm grade (starZMulCore parameters (rows 0) + zMulCore parameters (rows 1)) ≤
        (2 * coordinate) * total :=
      (originalGradeNorm_add_le grade _ _).trans
        ((add_le_add (starBound 0) (zBound 1)).trans_eq (by ring))
    have all (index : Fin 4) : originalGradeNorm grade (rawReconstructionCore parameters rows index) ≤
        weights index * total := by
      fin_cases index
      · change originalGradeNorm grade ((2 * Complex.I)⁻¹ • _) ≤ _
        rw [originalGradeNorm_smul]
        exact (mul_le_mul_of_nonneg_left pairSub (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm
      · change originalGradeNorm grade ((1 / 2 : ℂ) • _) ≤ _
        rw [originalGradeNorm_smul]
        exact (mul_le_mul_of_nonneg_left pairAdd (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm
      · change originalGradeNorm grade (rows 3) ≤ 1 * total
        simpa only [one_mul] using component 3
      · change originalGradeNorm grade (starZMulCore parameters (zMulCore parameters (rows 2))) ≤
          (coordinate * coordinate) * total
        exact (starZMulCore_bound _ grade).trans
          ((mul_le_mul_of_nonneg_left (zBound 2) nonnegative).trans_eq (mul_assoc _ _ _).symm)
    exact (Finset.sum_le_sum (fun index _ => all index)).trans_eq (Finset.sum_mul _ _ _).symm

theorem rawReconstructionCore_directional
    (mapping : JointState parameters → QuotientRows parameters)
    (base direction : JointState parameters) (derivative : QuotientRows parameters)
    (genuine : IsJointRowsDirectionalDerivative mapping base direction derivative) :
    IsJointRowsDirectionalDerivative (fun point => rawReconstructionCore parameters (mapping point))
      base direction (rawReconstructionCore parameters derivative) := by
  intro grade
  obtain ⟨constant, _, bound⟩ := rawReconstructionCore_rows_bound (parameters := parameters) grade
  have limit := (genuine grade).const_mul constant
  rw [mul_zero] at limit
  refine squeeze_zero (fun _ => rowsGradeNorm_nonneg _ _) (fun scalar => ?_) limit
  have estimate := bound
    ((scalar : ℂ)⁻¹ • (mapping (base + (scalar : ℂ) • direction) - mapping base) - derivative)
  simpa only [map_sub, map_smul] using estimate

end Grad.RawForward
