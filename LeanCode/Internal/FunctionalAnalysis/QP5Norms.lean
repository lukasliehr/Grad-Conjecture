import QP4ProjectionLaws

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.QuotientProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.AxisCore Grad.NonlinearProduct Grad.Constraints.Gauges

theorem ofCore_norm (parameters : PhaseParameters) (grade : ℕ) (field : ACore parameters 1) :
    ‖GradeCore.ofCoreLinear (grade := grade) field‖ = originalGradeNorm grade field :=
  rfl

theorem quotientNorm_nonneg (parameters : PhaseParameters) (grade : ℕ)
    (field : SmoothQuotient parameters) : 0 ≤ quotientNorm parameters grade field := norm_nonneg _

theorem quotientNorm_sq (parameters : PhaseParameters) (grade : ℕ)
    (field : SmoothQuotient parameters) :
    quotientNorm parameters grade field ^ 2 =
      ∑ coordinate : Fin 4, originalGradeNorm grade (field coordinate) ^ 2 := by
  unfold quotientNorm quotientEta
  rw [LinearMap.comp_apply, zEmbedding_norm_sq]
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, ofCore_norm]

theorem quotientNorm_component (parameters : PhaseParameters) (grade : ℕ)
    (field : SmoothQuotient parameters) (coordinate : Fin 4) :
    originalGradeNorm grade (field coordinate) ≤ quotientNorm parameters grade field := by
  have bound := zComponent_norm_le parameters grade coordinate (quotientEta parameters grade field)
  change ‖aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) (field coordinate))‖ ≤ _ at bound
  rw [(aGradeEta parameters).norm_map, ofCore_norm] at bound
  exact bound

theorem quotientNorm_le_two_mul (parameters : PhaseParameters) (grade : ℕ)
    (field : SmoothQuotient parameters) (bound : ℝ) (nonneg : 0 ≤ bound)
    (bounded : ∀ coordinate : Fin 4, originalGradeNorm grade (field coordinate) ≤ bound) :
    quotientNorm parameters grade field ≤ 2 * bound := by
  have squares : quotientNorm parameters grade field ^ 2 ≤ 4 * bound ^ 2 := by
    rw [quotientNorm_sq]
    calc (∑ coordinate : Fin 4, originalGradeNorm grade (field coordinate) ^ 2)
        ≤ ∑ _coordinate : Fin 4, bound ^ 2 := by
          apply Finset.sum_le_sum
          intro coordinate _
          exact pow_le_pow_left₀ (norm_nonneg _) (bounded coordinate) 2
      _ = 4 * bound ^ 2 := by simp
  have positive := quotientNorm_nonneg parameters grade field
  nlinarith

theorem quotientNorm_sub_le (parameters : PhaseParameters) (grade : ℕ)
    (first second : SmoothQuotient parameters) :
    quotientNorm parameters grade (first - second) ≤
      quotientNorm parameters grade first + quotientNorm parameters grade second := by
  unfold quotientNorm
  rw [map_sub]
  exact norm_sub_le _ _

theorem originalNorm_smul (grade : ℕ) (scalar : ℂ) (parameters : PhaseParameters)
    (field : ACore parameters 1) :
    originalGradeNorm grade (scalar • field) = ‖scalar‖ * originalGradeNorm grade field := by
  unfold originalGradeNorm
  rw [map_smul, norm_smul]

theorem originalNorm_angular (parameters : PhaseParameters) (grade : ℕ) (mode : ℤ)
    (field : ACore parameters 1) :
    originalGradeNorm grade (angularCore parameters mode field) ≤
      orthogonalGradeConstant grade * originalGradeNorm grade field := by
  simpa only [originalGradeNorm, ofCoreLinear_norm_coordinates] using
    angularCore_coordinates_bound parameters mode field grade

theorem originalNorm_reflection (parameters : PhaseParameters) (grade : ℕ)
    (field : ACore parameters 1) :
    originalGradeNorm grade (reflection parameters field) ≤
      orthogonalGradeConstant grade * originalGradeNorm grade field := by
  simpa only [originalGradeNorm, ofCoreLinear_norm_coordinates, reflection] using
    orthogonalCore_coordinates_bound parameters cartesianReflectionEquiv field grade

theorem meanPair_bound (parameters : PhaseParameters) (grade : ℕ)
    (field : SmoothQuotient parameters) :
    quotientNorm parameters grade (meanPair parameters field) ≤
      (2 * (1 + orthogonalGradeConstant grade)) * quotientNorm parameters grade field := by
  have positive := orthogonalGradeConstant_nonnegative grade
  have normPositive := quotientNorm_nonneg parameters grade field
  have component (index : Fin 4) := quotientNorm_component parameters grade field index
  have removed (index : Fin 4) :
      originalGradeNorm grade (field index - angularCore parameters 0 (field index)) ≤
        (1 + orthogonalGradeConstant grade) * quotientNorm parameters grade field := by
    have triangle := originalGradeNorm_sub_le grade (field index) (angularCore parameters 0 (field index))
    have angular := originalNorm_angular parameters grade 0 (field index)
    have scaled := mul_le_mul_of_nonneg_left (component index) positive
    nlinarith only [triangle, angular, scaled, component index]
  have bound := quotientNorm_le_two_mul parameters grade (meanPair parameters field)
    ((1 + orthogonalGradeConstant grade) * quotientNorm parameters grade field)
    (mul_nonneg (by positivity) normPositive) (by
      intro coordinate
      rw [meanPair_apply]
      fin_cases coordinate
      · exact (component 0).trans (by nlinarith)
      · exact (component 1).trans (by nlinarith)
      · exact removed 2
      · exact removed 3)
  nlinarith

theorem firstMode_bound (parameters : PhaseParameters) (grade : ℕ)
    (field : SmoothQuotient parameters) :
    originalGradeNorm grade (firstMode parameters field) ≤
      ((orthogonalGradeConstant grade + orthogonalGradeConstant grade ^ 2) / 2) *
        quotientNorm parameters grade field := by
  have positive := orthogonalGradeConstant_nonnegative grade
  have first := quotientNorm_component parameters grade field 0
  have second := quotientNorm_component parameters grade field 1
  rw [firstMode_apply, originalNorm_smul]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  have triangle := originalGradeNorm_add_le grade
    (angularCore parameters 1 (field 0))
    (reflection parameters (angularCore parameters (-1) (field 1)))
  have bound1 := originalNorm_angular parameters grade 1 (field 0)
  have bound2 := (originalNorm_reflection parameters grade
    (angularCore parameters (-1) (field 1))).trans
      (mul_le_mul_of_nonneg_left (originalNorm_angular parameters grade (-1) (field 1)) positive)
  nlinarith [mul_le_mul_of_nonneg_left first positive,
    mul_le_mul_of_nonneg_left second (sq_nonneg (orthogonalGradeConstant grade))]

theorem modeProjection_bound (parameters : PhaseParameters) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ field : SmoothQuotient parameters,
      quotientNorm parameters grade (modeProjection parameters field) ≤
        constant * quotientNorm parameters grade field := by
  let a := orthogonalGradeConstant grade
  let b := (a + a ^ 2) / 2
  have apos : 0 ≤ a := orthogonalGradeConstant_nonnegative grade
  have bpos : 0 ≤ b := by dsimp [b]; positivity
  refine ⟨2 * ((1 + a) * b), by positivity, ?_⟩
  intro field
  have np := quotientNorm_nonneg parameters grade field
  have first : originalGradeNorm grade (firstMode parameters field) ≤
      b * quotientNorm parameters grade field := firstMode_bound parameters grade field
  have second := (originalNorm_reflection parameters grade (firstMode parameters field)).trans
    (mul_le_mul_of_nonneg_left first apos)
  have estimate := quotientNorm_le_two_mul parameters grade (modeProjection parameters field)
    (((1 + a) * b) * quotientNorm parameters grade field) (by positivity) (by
      intro coordinate
      rw [modeProjection_apply]
      fin_cases coordinate
      · exact first.trans (by nlinarith [mul_nonneg apos (mul_nonneg bpos np)])
      · exact second.trans (by nlinarith [mul_nonneg bpos np])
      · change originalGradeNorm grade 0 ≤ _
        simp only [originalGradeNorm, map_zero, norm_zero]
        positivity
      · change originalGradeNorm grade 0 ≤ _
        simp only [originalGradeNorm, map_zero, norm_zero]
        positivity)
  nlinarith

end Grad.QuotientProjection
