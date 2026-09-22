import ClosedJetWordCoordinates

noncomputable section

open Grad.ClosedJets Grad.CartesianState
open scoped BigOperators

namespace Grad.Constraints

/-- Literal N2 constant, with unordered multi-indices counted once. -/
def orthogonalGradeConstant (grade : ℕ) : ℝ :=
  (2 : ℝ) ^ grade * Real.sqrt (Fintype.card (GradeMultiIndex grade))

theorem orthogonalGradeConstant_nonnegative (grade : ℕ) :
    0 ≤ orthogonalGradeConstant grade := by
  unfold orthogonalGradeConstant
  positivity

theorem orthogonal_grade_coordinate_bound {dimension grade : ℕ}
    (parameters : PhaseParameters) (cell : ℤ)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ClosedJet dimension)
    (index : GradeMultiIndex grade) :
    ‖cellGradeRowLinear parameters cell (orthogonalJet orthogonal field) index‖ ≤
      (2 : ℝ) ^ grade * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
  rw [cellGradeRowLinear_apply, norm_smul, Complex.norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (cellFrequency_pos cell)]
  exact weighted_orthogonal_word_norm_le parameters cell orthogonal field
    index.property (cartesianMultiIndexWord index.toCartesian)

theorem orthogonal_grade_row_bound {dimension grade : ℕ}
    (parameters : PhaseParameters) (cell : ℤ)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ClosedJet dimension) :
    ‖cellGradeRowLinear (grade := grade) parameters cell (orthogonalJet orthogonal field)‖ ≤
      orthogonalGradeConstant grade * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
  let row := cellGradeRowLinear (grade := grade) parameters cell (orthogonalJet orthogonal field)
  let bound := (2 : ℝ) ^ grade * ‖cellGradeRowLinear (grade := grade) parameters cell field‖
  have boundNonnegative : 0 ≤ bound := by dsimp [bound]; positivity
  have squareBound : ‖row‖ ^ 2 ≤ (Fintype.card (GradeMultiIndex grade) : ℝ) * bound ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _index : GradeMultiIndex grade, bound ^ 2 := by
        apply Finset.sum_le_sum
        intro index _
        exact pow_le_pow_left₀ (norm_nonneg (row index))
          (orthogonal_grade_coordinate_bound parameters cell orthogonal field index) 2
      _ = _ := by simp
  have squareRoot := Real.sq_sqrt
    (show (0 : ℝ) ≤ Fintype.card (GradeMultiIndex grade) by positivity)
  have rootNonnegative := Real.sqrt_nonneg (Fintype.card (GradeMultiIndex grade) : ℝ)
  have productNonnegative : 0 ≤ Real.sqrt (Fintype.card (GradeMultiIndex grade) : ℝ) * bound :=
    mul_nonneg rootNonnegative boundNonnegative
  have result : ‖row‖ ≤ Real.sqrt (Fintype.card (GradeMultiIndex grade) : ℝ) * bound := by
    nlinarith [sq_nonneg (‖row‖ - Real.sqrt (Fintype.card (GradeMultiIndex grade) : ℝ) * bound)]
  unfold orthogonalGradeConstant
  dsimp [bound, row] at result
  nlinarith [result]

end Grad.Constraints
