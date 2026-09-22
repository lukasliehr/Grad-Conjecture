import AXF2RadialProfileFormulas

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 400000

namespace Grad.FlatSourceProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.NonlinearQuotientBounds Grad.QuotientProjection Grad.ChartAxisLift
open Grad.NonlinearProduct

variable {parameters : PhaseParameters} {dimension : ℕ}

theorem originalNorm_angular_any (grade : ℕ) (mode : ℤ)
    (field : ACore parameters dimension) :
    originalGradeNorm grade (angularCore parameters mode field) ≤
      orthogonalGradeConstant grade * originalGradeNorm grade field := by
  simpa only [originalGradeNorm, Gauges.ofCoreLinear_norm_coordinates] using
    angularCore_coordinates_bound parameters mode field grade

theorem radialValueInsertion_bound (grade : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ data : Grad.AxisCore.AxisSmoothCore parameters dimension,
      originalGradeNorm (grade + 1) (radialValueInsertion data) ≤
        bound * ‖Grad.AxisCore.axisEta parameters dimension grade data‖ := by
  obtain ⟨bound, nonneg, estimate⟩ := insertZero_bound (parameters := parameters) (dimension := dimension) grade
  refine ⟨orthogonalGradeConstant (grade + 1) * bound,
    mul_nonneg (orthogonalGradeConstant_nonnegative _) nonneg, ?_⟩
  intro data
  exact (originalNorm_angular_any (grade + 1) 0 (insertZero data)).trans
    ((mul_le_mul_of_nonneg_left (estimate data) (orthogonalGradeConstant_nonnegative _)).trans_eq
      (mul_assoc _ _ _).symm)

theorem coordinateProfilePair_bound (grade : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ data : Grad.AxisCore.AxisSmoothCore parameters dimension,
      originalGradeNorm (grade + 2) (insertOne 0 data + Complex.I • insertOne 1 data) ≤
          bound * ‖Grad.AxisCore.axisEta parameters dimension grade data‖ ∧
      originalGradeNorm (grade + 2) (insertOne 0 data - Complex.I • insertOne 1 data) ≤
          bound * ‖Grad.AxisCore.axisEta parameters dimension grade data‖ := by
  obtain ⟨first, firstNonneg, firstBound⟩ := insertOne_bound (parameters := parameters) (dimension := dimension) 0 grade
  obtain ⟨second, secondNonneg, secondBound⟩ := insertOne_bound (parameters := parameters) (dimension := dimension) 1 grade
  refine ⟨first + second, add_nonneg firstNonneg secondNonneg, ?_⟩
  intro data
  have plus := Grad.NonlinearQuotientBounds.originalGradeNorm_add_le (grade + 2) (insertOne 0 data) (Complex.I • insertOne 1 data)
  have minus := Grad.NonlinearQuotientBounds.originalGradeNorm_sub_le (grade + 2) (insertOne 0 data) (Complex.I • insertOne 1 data)
  rw [originalGradeNorm_smul, Complex.norm_I, one_mul] at plus minus
  constructor
  · exact plus.trans ((add_le_add (firstBound data) (secondBound data)).trans_eq (add_mul _ _ _).symm)
  · exact minus.trans ((add_le_add (firstBound data) (secondBound data)).trans_eq (add_mul _ _ _).symm)

theorem radialFirstInsertion_bound (coordinate : Fin 2) (grade : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ data : Grad.AxisCore.AxisSmoothCore parameters dimension,
      originalGradeNorm (grade + 2) (radialFirstInsertion coordinate data) ≤
        bound * ‖Grad.AxisCore.axisEta parameters dimension grade data‖ := by
  obtain ⟨bound, nonneg, estimate⟩ := coordinateProfilePair_bound (parameters := parameters) (dimension := dimension) grade
  let constant := orthogonalGradeConstant (grade + 2) * bound
  refine ⟨constant, mul_nonneg (orthogonalGradeConstant_nonnegative _) nonneg, ?_⟩
  intro data
  have plus : originalGradeNorm (grade + 2)
      (angularCore parameters 1 (insertOne 0 data + Complex.I • insertOne 1 data)) ≤
      constant * ‖Grad.AxisCore.axisEta parameters dimension grade data‖ :=
    (originalNorm_angular_any _ _ _).trans
      ((mul_le_mul_of_nonneg_left (estimate data).1 (orthogonalGradeConstant_nonnegative _)).trans_eq
        (mul_assoc _ _ _).symm)
  have minus : originalGradeNorm (grade + 2)
      (angularCore parameters (-1) (insertOne 0 data - Complex.I • insertOne 1 data)) ≤
      constant * ‖Grad.AxisCore.axisEta parameters dimension grade data‖ :=
    (originalNorm_angular_any _ _ _).trans
      ((mul_le_mul_of_nonneg_left (estimate data).2 (orthogonalGradeConstant_nonnegative _)).trans_eq
        (mul_assoc _ _ _).symm)
  fin_cases coordinate
  · change originalGradeNorm (grade + 2) (radialFirstInsertion 0 data) ≤ _
    rw [radialFirstInsertion_zero_formula, originalGradeNorm_smul]
    norm_num only [norm_div, norm_one, Complex.norm_ofNat]
    have triangle := Grad.NonlinearQuotientBounds.originalGradeNorm_add_le (grade + 2)
      (angularCore parameters 1 (insertOne 0 data + Complex.I • insertOne 1 data))
      (angularCore parameters (-1) (insertOne 0 data - Complex.I • insertOne 1 data))
    linarith
  · change originalGradeNorm (grade + 2) (radialFirstInsertion 1 data) ≤ _
    rw [radialFirstInsertion_one_formula]
    have triangle := Grad.NonlinearQuotientBounds.originalGradeNorm_add_le (grade + 2)
      ((-(Complex.I / 2)) • angularCore parameters 1 (insertOne 0 data + Complex.I • insertOne 1 data))
      ((Complex.I / 2) • angularCore parameters (-1) (insertOne 0 data - Complex.I • insertOne 1 data))
    rw [originalGradeNorm_smul, originalGradeNorm_smul] at triangle
    norm_num only [norm_neg, norm_div, Complex.norm_I, Complex.norm_ofNat] at triangle
    linarith

end Grad.FlatSourceProjection
