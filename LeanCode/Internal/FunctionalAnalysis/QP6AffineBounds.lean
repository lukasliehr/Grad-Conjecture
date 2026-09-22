import QP5Norms

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.QuotientProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.AxisCore Grad.NonlinearProduct

theorem affineTrace_bound (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ field : SmoothQuotient parameters,
      ‖axisEta parameters 1 (grade - 2) (affineTrace parameters field)‖ ≤
        constant * quotientNorm parameters grade field := by
  let c := 6 * diskSupConstant
  have cp : 0 ≤ c := mul_nonneg (by norm_num) diskSupConstant_pos.le
  refine ⟨c, cp, ?_⟩
  intro field
  have bound (direction : Fin 2) (coordinate : Fin 4) :
      ‖axisEta parameters 1 (grade - 2) (traceFirst direction (field coordinate))‖ ≤
        c * quotientNorm parameters grade field :=
    (traceFirst_contract direction (field coordinate) grade large).trans
      (mul_le_mul_of_nonneg_left (quotientNorm_component parameters grade field coordinate) cp)
  change ‖axisEta parameters 1 (grade - 2) ((4 * Complex.I)⁻¹ •
    ((traceFirst 0 (field 0) - Complex.I • traceFirst 1 (field 0)) -
      (traceFirst 0 (field 1) + Complex.I • traceFirst 1 (field 1))))‖ ≤ _
  simp only [map_smul, map_sub, map_add, norm_smul, norm_inv, norm_mul,
    Complex.norm_ofNat, Complex.norm_I, mul_one]
  have h0 := norm_sub_le
    (axisEta parameters 1 (grade - 2) (traceFirst 0 (field 0)))
    (Complex.I • axisEta parameters 1 (grade - 2) (traceFirst 1 (field 0)))
  have h1 := norm_add_le
    (axisEta parameters 1 (grade - 2) (traceFirst 0 (field 1)))
    (Complex.I • axisEta parameters 1 (grade - 2) (traceFirst 1 (field 1)))
  have h2 := norm_sub_le
    (axisEta parameters 1 (grade - 2) (traceFirst 0 (field 0)) -
      Complex.I • axisEta parameters 1 (grade - 2) (traceFirst 1 (field 0)))
    (axisEta parameters 1 (grade - 2) (traceFirst 0 (field 1)) +
      Complex.I • axisEta parameters 1 (grade - 2) (traceFirst 1 (field 1)))
  simp only [norm_smul, Complex.norm_I, one_mul] at h0 h1
  nlinarith [bound 0 0, bound 1 0, bound 0 1, bound 1 1]

theorem affineInsertion_bound (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ family : AxisSmoothCore parameters 1,
      quotientNorm parameters grade (affineInsertion parameters family) ≤
        constant * ‖axisEta parameters 1 (grade - 2) family‖ := by
  obtain ⟨c0, p0, b0⟩ := insertOne_bound (parameters := parameters) (dimension := 1) 0 (grade - 2)
  obtain ⟨c1, p1, b1⟩ := insertOne_bound (parameters := parameters) (dimension := 1) 1 (grade - 2)
  have shift : grade - 2 + 2 = grade := Nat.sub_add_cancel (by omega)
  rw [shift] at b0 b1
  refine ⟨2 * (c0 + c1), by positivity, ?_⟩
  intro family
  have np := norm_nonneg (axisEta parameters 1 (grade - 2) family)
  have plus : originalGradeNorm grade
      (Complex.I • (insertOne 0 family + Complex.I • insertOne 1 family)) ≤
      (c0 + c1) * ‖axisEta parameters 1 (grade - 2) family‖ := by
    rw [originalNorm_smul, Complex.norm_I, one_mul]
    have triangle := originalGradeNorm_add_le grade (insertOne 0 family) (Complex.I • insertOne 1 family)
    rw [originalNorm_smul, Complex.norm_I, one_mul] at triangle
    nlinarith [b0 family, b1 family]
  have minus : originalGradeNorm grade
      ((-Complex.I) • (insertOne 0 family - Complex.I • insertOne 1 family)) ≤
      (c0 + c1) * ‖axisEta parameters 1 (grade - 2) family‖ := by
    rw [originalNorm_smul, norm_neg, Complex.norm_I, one_mul]
    have triangle := originalGradeNorm_sub_le grade (insertOne 0 family) (Complex.I • insertOne 1 family)
    rw [originalNorm_smul, Complex.norm_I, one_mul] at triangle
    nlinarith [b0 family, b1 family]
  have estimate := quotientNorm_le_two_mul parameters grade (affineInsertion parameters family)
    ((c0 + c1) * ‖axisEta parameters 1 (grade - 2) family‖) (by positivity) (by
      intro coordinate
      fin_cases coordinate
      · exact plus
      · exact minus
      · change originalGradeNorm grade 0 ≤ _
        simp only [originalGradeNorm, map_zero, norm_zero]
        positivity
      · change originalGradeNorm grade 0 ≤ _
        simp only [originalGradeNorm, map_zero, norm_zero]
        positivity)
  nlinarith

theorem quotientProjection_bound (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ field : SmoothQuotient parameters,
      quotientNorm parameters grade (quotientProjection parameters field) ≤
        constant * quotientNorm parameters grade field := by
  obtain ⟨ct, pt, bt⟩ := affineTrace_bound parameters grade large
  obtain ⟨ce, pe, be⟩ := affineInsertion_bound parameters grade large
  obtain ⟨ck, pk, bk⟩ := modeProjection_bound parameters grade
  have po := orthogonalGradeConstant_nonnegative grade
  refine ⟨2 * (1 + orthogonalGradeConstant grade) + ck + ce * ct, by positivity, ?_⟩
  intro field
  rw [quotientProjection_apply]
  have pair := quotientNorm_sub_le parameters grade (meanPair parameters field) (modeProjection parameters field)
  have total := quotientNorm_sub_le parameters grade
    (meanPair parameters field - modeProjection parameters field)
    (affineInsertion parameters (affineTrace parameters field))
  have aff := (be (affineTrace parameters field)).trans
    (mul_le_mul_of_nonneg_left (bt field) pe)
  nlinarith [meanPair_bound parameters grade field, bk field]

end Grad.QuotientProjection
