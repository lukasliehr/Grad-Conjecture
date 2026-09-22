import AXF6FlatRange

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.NonlinearQuotientBounds Grad.QuotientProjection Grad.AxisCore Grad.NonlinearProduct

theorem radialAffineInsertion_bound (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ family : AxisSmoothCore parameters 1,
      quotientNorm parameters grade (radialAffineInsertion family) ≤
        constant * ‖axisEta parameters 1 (grade - 2) family‖ := by
  obtain ⟨c0, p0, b0⟩ := radialFirstInsertion_bound (parameters := parameters) (dimension := 1) 0 (grade - 2)
  obtain ⟨c1, p1, b1⟩ := radialFirstInsertion_bound (parameters := parameters) (dimension := 1) 1 (grade - 2)
  have shift : grade - 2 + 2 = grade := Nat.sub_add_cancel (by omega)
  rw [shift] at b0 b1
  refine ⟨2 * (c0 + c1), by positivity, ?_⟩
  intro family
  have np := norm_nonneg (axisEta parameters 1 (grade - 2) family)
  have plus : originalGradeNorm grade
      (Complex.I • (radialFirstInsertion 0 family + Complex.I • radialFirstInsertion 1 family)) ≤
      (c0 + c1) * ‖axisEta parameters 1 (grade - 2) family‖ := by
    rw [originalNorm_smul, Complex.norm_I, one_mul]
    have triangle := Grad.NonlinearQuotientBounds.originalGradeNorm_add_le grade (radialFirstInsertion 0 family) (Complex.I • radialFirstInsertion 1 family)
    rw [originalNorm_smul, Complex.norm_I, one_mul] at triangle
    nlinarith [b0 family, b1 family]
  have minus : originalGradeNorm grade
      ((-Complex.I) • (radialFirstInsertion 0 family - Complex.I • radialFirstInsertion 1 family)) ≤
      (c0 + c1) * ‖axisEta parameters 1 (grade - 2) family‖ := by
    rw [originalNorm_smul, norm_neg, Complex.norm_I, one_mul]
    have triangle := Grad.NonlinearQuotientBounds.originalGradeNorm_sub_le grade (radialFirstInsertion 0 family) (Complex.I • radialFirstInsertion 1 family)
    rw [originalNorm_smul, Complex.norm_I, one_mul] at triangle
    nlinarith [b0 family, b1 family]
  have estimate := quotientNorm_le_two_mul parameters grade (radialAffineInsertion family)
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

theorem valueCorrection_bound (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ source : SmoothQuotient parameters,
      quotientNorm parameters grade (valueCorrection source) ≤
        constant * quotientNorm parameters grade source := by
  obtain ⟨bound, nonneg, estimate⟩ := radialValueInsertion_bound
    (parameters := parameters) (dimension := 1) (grade - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ grade)] at estimate
  let traceConstant := 6 * diskSupConstant
  have traceNonneg : 0 ≤ traceConstant := mul_nonneg (by norm_num) diskSupConstant_pos.le
  let constant := bound * traceConstant
  have constantNonneg : 0 ≤ constant := mul_nonneg nonneg traceNonneg
  refine ⟨2 * constant, mul_nonneg (by norm_num) constantNonneg, ?_⟩
  intro source
  have term (coordinate : Fin 4) :
      originalGradeNorm grade (radialValueInsertion (traceZero (source coordinate))) ≤
        constant * quotientNorm parameters grade source := by
    have traceBound := (traceZero_contract (source coordinate) grade (by omega)).trans
      (mul_le_mul_of_nonneg_left (quotientNorm_component parameters grade source coordinate) traceNonneg)
    exact (estimate (traceZero (source coordinate))).trans
      ((mul_le_mul_of_nonneg_left traceBound nonneg).trans_eq (mul_assoc _ _ _).symm)
  have result := quotientNorm_le_two_mul parameters grade (valueCorrection source)
    (constant * quotientNorm parameters grade source)
    (mul_nonneg constantNonneg (quotientNorm_nonneg _ _ _)) (by
      intro coordinate
      fin_cases coordinate
      · exact term 0
      · exact term 1
      · change originalGradeNorm grade 0 ≤ _
        simp only [originalGradeNorm, map_zero, norm_zero]
        exact mul_nonneg constantNonneg (quotientNorm_nonneg _ _ _)
      · change originalGradeNorm grade 0 ≤ _
        simp only [originalGradeNorm, map_zero, norm_zero]
        exact mul_nonneg constantNonneg (quotientNorm_nonneg _ _ _))
  exact result.trans_eq (mul_assoc _ _ _).symm

theorem scalarGradientCorrection_bound (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ field : ACore parameters 1,
      originalGradeNorm grade (scalarGradientCorrection field) ≤ constant * originalGradeNorm grade field := by
  obtain ⟨first, firstNonneg, firstBound⟩ := radialFirstInsertion_bound
    (parameters := parameters) (dimension := 1) 0 (grade - 2)
  obtain ⟨second, secondNonneg, secondBound⟩ := radialFirstInsertion_bound
    (parameters := parameters) (dimension := 1) 1 (grade - 2)
  rw [Nat.sub_add_cancel (by omega : 2 ≤ grade)] at firstBound secondBound
  let traceConstant := 6 * diskSupConstant
  have traceNonneg : 0 ≤ traceConstant := mul_nonneg (by norm_num) diskSupConstant_pos.le
  refine ⟨(first + second) * traceConstant,
    mul_nonneg (add_nonneg firstNonneg secondNonneg) traceNonneg, ?_⟩
  intro field
  have left := (firstBound (traceFirst 0 field)).trans
    (mul_le_mul_of_nonneg_left (traceFirst_contract 0 field grade large) firstNonneg)
  have right := (secondBound (traceFirst 1 field)).trans
    (mul_le_mul_of_nonneg_left (traceFirst_contract 1 field grade large) secondNonneg)
  rw [scalarGradientCorrection_apply]
  exact (Grad.NonlinearQuotientBounds.originalGradeNorm_add_le grade _ _).trans
    ((add_le_add left right).trans_eq (by dsimp [traceConstant]; ring))

theorem fourthCorrection_bound (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ source : SmoothQuotient parameters,
      quotientNorm parameters grade (fourthCorrection source) ≤ constant * quotientNorm parameters grade source := by
  obtain ⟨bound, nonneg, estimate⟩ := scalarGradientCorrection_bound parameters grade large
  let constant := bound * (1 + orthogonalGradeConstant grade)
  have angularNonneg := orthogonalGradeConstant_nonnegative grade
  have constantNonneg : 0 ≤ constant := mul_nonneg nonneg (by positivity)
  refine ⟨2 * constant, mul_nonneg (by norm_num) constantNonneg, ?_⟩
  intro source
  have meanBound : originalGradeNorm grade (source 3 - angularCore parameters 0 (source 3)) ≤
      (1 + orthogonalGradeConstant grade) * quotientNorm parameters grade source := by
    have angular := (originalNorm_angular parameters grade 0 (source 3)).trans
      (mul_le_mul_of_nonneg_left (quotientNorm_component parameters grade source 3) angularNonneg)
    exact (Grad.NonlinearQuotientBounds.originalGradeNorm_sub_le grade _ _).trans
      ((add_le_add (quotientNorm_component parameters grade source 3) angular).trans_eq (by ring))
  have term := (estimate (source 3 - angularCore parameters 0 (source 3))).trans
    (mul_le_mul_of_nonneg_left meanBound nonneg)
  have term' : originalGradeNorm grade
      (scalarGradientCorrection (source 3 - angularCore parameters 0 (source 3))) ≤
      constant * quotientNorm parameters grade source := term.trans_eq (mul_assoc _ _ _).symm
  have result := quotientNorm_le_two_mul parameters grade (fourthCorrection source)
    (constant * quotientNorm parameters grade source)
    (mul_nonneg constantNonneg (quotientNorm_nonneg _ _ _)) (by
      intro coordinate
      fin_cases coordinate
      · change originalGradeNorm grade 0 ≤ _
        simp only [originalGradeNorm, map_zero, norm_zero]
        exact mul_nonneg constantNonneg (quotientNorm_nonneg _ _ _)
      · change originalGradeNorm grade 0 ≤ _
        simp only [originalGradeNorm, map_zero, norm_zero]
        exact mul_nonneg constantNonneg (quotientNorm_nonneg _ _ _)
      · change originalGradeNorm grade 0 ≤ _
        simp only [originalGradeNorm, map_zero, norm_zero]
        exact mul_nonneg constantNonneg (quotientNorm_nonneg _ _ _)
      · exact term')
  exact result.trans_eq (mul_assoc _ _ _).symm

end Grad.FlatSourceProjection
