import TameRootMajorant

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! The quadratic remainder estimate: the decorated triple-product bound,
the double binomial collapse, and the final `t²` bound for the root curve
remainder in every graded envelope. -/

variable {parameters : PhaseParameters}

/-- The graded triple-product bound with separated payload bases. -/
theorem rootTriple_envelope_le {x : TameCoefficient parameters}
    (small : coefficientEnvelope 0 x < 1) (u w : TameCoefficient parameters)
    (grade a b c : ℕ) :
    coefficientEnvelope grade (x ^ a * (u ^ b * w ^ c)) ≤
      6 * 4 ^ grade * ((a + b + c + 1 : ℕ) : ℝ) ^ (grade + 1) *
        rootEnvelopeScale x u w grade * rootEnvelopeScale x u w 0 ^ 2 *
        (rootSmallRadius x ^ a * rootDirectionSize u ^ b * rootDirectionSize w ^ c) := by
  set scaleG := rootEnvelopeScale x u w grade with scaleG_def
  set scaleZ := rootEnvelopeScale x u w 0 with scaleZ_def
  set radius := rootSmallRadius x with radius_def
  set sizeU := rootDirectionSize u with sizeU_def
  set sizeW := rootDirectionSize w with sizeW_def
  have scaleG_nonneg : 0 ≤ scaleG := rootEnvelopeScale_nonneg x u w grade
  have scaleZ_nonneg : 0 ≤ scaleZ := rootEnvelopeScale_nonneg x u w 0
  have radius_nonneg : 0 ≤ radius := (rootSmallRadius_pos x).le
  have sizeU_nonneg : 0 ≤ sizeU := (rootDirectionSize_pos u).le
  have sizeW_nonneg : 0 ≤ sizeW := (rootDirectionSize_pos w).le
  have powA_nonneg : 0 ≤ radius ^ a := pow_nonneg radius_nonneg a
  have powB_nonneg : 0 ≤ sizeU ^ b := pow_nonneg sizeU_nonneg b
  have powC_nonneg : 0 ≤ sizeW ^ c := pow_nonneg sizeW_nonneg c
  have castA_le : ((a + 1 : ℕ) : ℝ) ^ (grade + 1) ≤
      ((a + b + c + 1 : ℕ) : ℝ) ^ (grade + 1) := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast by omega
  have castB_le : ((b + 1 : ℕ) : ℝ) ^ (grade + 1) ≤
      ((a + b + c + 1 : ℕ) : ℝ) ^ (grade + 1) := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast by omega
  have castC_le : ((c + 1 : ℕ) : ℝ) ^ (grade + 1) ≤
      ((a + b + c + 1 : ℕ) : ℝ) ^ (grade + 1) := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast by omega
  have castTotal_nonneg : (0 : ℝ) ≤ ((a + b + c + 1 : ℕ) : ℝ) ^ (grade + 1) :=
    pow_nonneg (Nat.cast_nonneg _) _
  have boundE₁ := base_pow_envelope_le small u w grade a
  have boundE₂ := direction_pow_envelope_le x u w u
    (fun whichGrade => envelope_u_le_rootEnvelopeScale x u w whichGrade) grade b
  have boundE₃ := direction_pow_envelope_le x u w w
    (fun whichGrade => envelope_w_le_rootEnvelopeScale x u w whichGrade) grade c
  have boundF₁ := base_pow_envelope_zero_le small u w a
  have boundF₂ := direction_pow_envelope_zero_le x u w u b
  have boundF₃ := direction_pow_envelope_zero_le x u w w c
  have nonnegE₁ := coefficientEnvelope_nonneg grade (x ^ a)
  have nonnegE₂ := coefficientEnvelope_nonneg grade (u ^ b)
  have nonnegE₃ := coefficientEnvelope_nonneg grade (w ^ c)
  have nonnegF₁ := coefficientEnvelope_nonneg 0 (x ^ a)
  have nonnegF₂ := coefficientEnvelope_nonneg 0 (u ^ b)
  have nonnegF₃ := coefficientEnvelope_nonneg 0 (w ^ c)
  have zeroSplit : coefficientEnvelope 0 (u ^ b * w ^ c) ≤
      (scaleZ * sizeU ^ b) * (scaleZ * sizeW ^ c) :=
    (tameMul_envelope_zero_le _ _).trans (mul_le_mul boundF₂ boundF₃ nonnegF₃
      (by positivity))
  have gradeSplit : coefficientEnvelope grade (u ^ b * w ^ c) ≤
      (2 : ℝ) ^ grade * ((2 * ((b + 1 : ℕ) : ℝ) ^ (grade + 1) * sizeU ^ b * scaleG) *
          (scaleZ * sizeW ^ c) +
        (scaleZ * sizeU ^ b) * (2 * ((c + 1 : ℕ) : ℝ) ^ (grade + 1) * sizeW ^ c * scaleG)) := by
    apply (tameMul_envelope_le grade _ _).trans
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) grade)
    apply add_le_add
    · exact mul_le_mul boundE₂ boundF₃ nonnegF₃ (by positivity)
    · exact mul_le_mul boundF₂ boundE₃ nonnegE₃ (by positivity)
  have mainSplit : coefficientEnvelope grade (x ^ a * (u ^ b * w ^ c)) ≤
      (2 : ℝ) ^ grade *
        (coefficientEnvelope grade (x ^ a) * coefficientEnvelope 0 (u ^ b * w ^ c) +
          coefficientEnvelope 0 (x ^ a) * coefficientEnvelope grade (u ^ b * w ^ c)) :=
    tameMul_envelope_le grade _ _
  have first_piece : coefficientEnvelope grade (x ^ a) *
      coefficientEnvelope 0 (u ^ b * w ^ c) ≤
      2 * ((a + b + c + 1 : ℕ) : ℝ) ^ (grade + 1) * scaleG * scaleZ ^ 2 *
        (radius ^ a * sizeU ^ b * sizeW ^ c) := by
    calc coefficientEnvelope grade (x ^ a) * coefficientEnvelope 0 (u ^ b * w ^ c)
        ≤ (2 * ((a + 1 : ℕ) : ℝ) ^ (grade + 1) * radius ^ a * scaleG) *
            ((scaleZ * sizeU ^ b) * (scaleZ * sizeW ^ c)) :=
          mul_le_mul boundE₁ zeroSplit (coefficientEnvelope_nonneg 0 _) (by positivity)
      _ ≤ (2 * ((a + b + c + 1 : ℕ) : ℝ) ^ (grade + 1) * radius ^ a * scaleG) *
            ((scaleZ * sizeU ^ b) * (scaleZ * sizeW ^ c)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ scaleG_nonneg
          apply mul_le_mul_of_nonneg_right _ powA_nonneg
          exact mul_le_mul_of_nonneg_left castA_le (by norm_num)
      _ = _ := by ring
  have second_piece : coefficientEnvelope 0 (x ^ a) *
      coefficientEnvelope grade (u ^ b * w ^ c) ≤
      (2 : ℝ) ^ grade * (4 * ((a + b + c + 1 : ℕ) : ℝ) ^ (grade + 1) * scaleG * scaleZ ^ 2 *
        (radius ^ a * sizeU ^ b * sizeW ^ c)) := by
    calc coefficientEnvelope 0 (x ^ a) * coefficientEnvelope grade (u ^ b * w ^ c)
        ≤ (scaleZ * radius ^ a) * ((2 : ℝ) ^ grade *
            ((2 * ((b + 1 : ℕ) : ℝ) ^ (grade + 1) * sizeU ^ b * scaleG) *
              (scaleZ * sizeW ^ c) +
            (scaleZ * sizeU ^ b) *
              (2 * ((c + 1 : ℕ) : ℝ) ^ (grade + 1) * sizeW ^ c * scaleG))) :=
          mul_le_mul boundF₁ gradeSplit (coefficientEnvelope_nonneg grade _) (by positivity)
      _ ≤ _ := by
          have inner_le : (2 * ((b + 1 : ℕ) : ℝ) ^ (grade + 1) * sizeU ^ b * scaleG) *
                (scaleZ * sizeW ^ c) +
              (scaleZ * sizeU ^ b) *
                (2 * ((c + 1 : ℕ) : ℝ) ^ (grade + 1) * sizeW ^ c * scaleG) ≤
              4 * ((a + b + c + 1 : ℕ) : ℝ) ^ (grade + 1) * scaleG * scaleZ *
                (sizeU ^ b * sizeW ^ c) := by
            have partB : (2 * ((b + 1 : ℕ) : ℝ) ^ (grade + 1) * sizeU ^ b * scaleG) *
                (scaleZ * sizeW ^ c) ≤
                2 * ((a + b + c + 1 : ℕ) : ℝ) ^ (grade + 1) * scaleG * scaleZ *
                  (sizeU ^ b * sizeW ^ c) := by
              calc (2 * ((b + 1 : ℕ) : ℝ) ^ (grade + 1) * sizeU ^ b * scaleG) *
                    (scaleZ * sizeW ^ c)
                  = 2 * ((b + 1 : ℕ) : ℝ) ^ (grade + 1) * scaleG * scaleZ *
                      (sizeU ^ b * sizeW ^ c) := by ring
                _ ≤ _ := by
                    apply mul_le_mul_of_nonneg_right _ (by positivity)
                    apply mul_le_mul_of_nonneg_right _ scaleZ_nonneg
                    apply mul_le_mul_of_nonneg_right _ scaleG_nonneg
                    exact mul_le_mul_of_nonneg_left castB_le (by norm_num)
            have partC : (scaleZ * sizeU ^ b) *
                (2 * ((c + 1 : ℕ) : ℝ) ^ (grade + 1) * sizeW ^ c * scaleG) ≤
                2 * ((a + b + c + 1 : ℕ) : ℝ) ^ (grade + 1) * scaleG * scaleZ *
                  (sizeU ^ b * sizeW ^ c) := by
              calc (scaleZ * sizeU ^ b) *
                    (2 * ((c + 1 : ℕ) : ℝ) ^ (grade + 1) * sizeW ^ c * scaleG)
                  = 2 * ((c + 1 : ℕ) : ℝ) ^ (grade + 1) * scaleG * scaleZ *
                      (sizeU ^ b * sizeW ^ c) := by ring
                _ ≤ _ := by
                    apply mul_le_mul_of_nonneg_right _ (by positivity)
                    apply mul_le_mul_of_nonneg_right _ scaleZ_nonneg
                    apply mul_le_mul_of_nonneg_right _ scaleG_nonneg
                    exact mul_le_mul_of_nonneg_left castC_le (by norm_num)
            calc (2 * ((b + 1 : ℕ) : ℝ) ^ (grade + 1) * sizeU ^ b * scaleG) *
                  (scaleZ * sizeW ^ c) +
                (scaleZ * sizeU ^ b) *
                  (2 * ((c + 1 : ℕ) : ℝ) ^ (grade + 1) * sizeW ^ c * scaleG)
                ≤ 2 * ((a + b + c + 1 : ℕ) : ℝ) ^ (grade + 1) * scaleG * scaleZ *
                    (sizeU ^ b * sizeW ^ c) +
                  2 * ((a + b + c + 1 : ℕ) : ℝ) ^ (grade + 1) * scaleG * scaleZ *
                    (sizeU ^ b * sizeW ^ c) := add_le_add partB partC
              _ = _ := by ring
          calc (scaleZ * radius ^ a) * ((2 : ℝ) ^ grade *
                ((2 * ((b + 1 : ℕ) : ℝ) ^ (grade + 1) * sizeU ^ b * scaleG) *
                  (scaleZ * sizeW ^ c) +
                (scaleZ * sizeU ^ b) *
                  (2 * ((c + 1 : ℕ) : ℝ) ^ (grade + 1) * sizeW ^ c * scaleG)))
              ≤ (scaleZ * radius ^ a) * ((2 : ℝ) ^ grade *
                  (4 * ((a + b + c + 1 : ℕ) : ℝ) ^ (grade + 1) * scaleG * scaleZ *
                    (sizeU ^ b * sizeW ^ c))) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact mul_le_mul_of_nonneg_left inner_le (pow_nonneg (by norm_num) grade)
            _ = _ := by ring
  have two_le_four : ((2 : ℝ)) ^ grade ≤ (4 : ℝ) ^ grade := by
    apply pow_le_pow_left₀ (by norm_num)
    norm_num
  calc coefficientEnvelope grade (x ^ a * (u ^ b * w ^ c))
      ≤ (2 : ℝ) ^ grade *
          (coefficientEnvelope grade (x ^ a) * coefficientEnvelope 0 (u ^ b * w ^ c) +
            coefficientEnvelope 0 (x ^ a) * coefficientEnvelope grade (u ^ b * w ^ c)) :=
        mainSplit
    _ ≤ (2 : ℝ) ^ grade *
          (2 * ((a + b + c + 1 : ℕ) : ℝ) ^ (grade + 1) * scaleG * scaleZ ^ 2 *
            (radius ^ a * sizeU ^ b * sizeW ^ c) +
          (2 : ℝ) ^ grade * (4 * ((a + b + c + 1 : ℕ) : ℝ) ^ (grade + 1) * scaleG *
            scaleZ ^ 2 * (radius ^ a * sizeU ^ b * sizeW ^ c))) := by
        apply mul_le_mul_of_nonneg_left (add_le_add first_piece second_piece)
          (pow_nonneg (by norm_num) grade)
    _ ≤ (4 : ℝ) ^ grade * (2 * ((a + b + c + 1 : ℕ) : ℝ) ^ (grade + 1) * scaleG *
          scaleZ ^ 2 * (radius ^ a * sizeU ^ b * sizeW ^ c)) +
        (4 : ℝ) ^ grade * (4 * ((a + b + c + 1 : ℕ) : ℝ) ^ (grade + 1) * scaleG *
          scaleZ ^ 2 * (radius ^ a * sizeU ^ b * sizeW ^ c)) := by
        have piece_nonneg : (0 : ℝ) ≤ 2 * ((a + b + c + 1 : ℕ) : ℝ) ^ (grade + 1) *
            scaleG * scaleZ ^ 2 * (radius ^ a * sizeU ^ b * sizeW ^ c) := by positivity
        have piece4_nonneg : (0 : ℝ) ≤ 4 * ((a + b + c + 1 : ℕ) : ℝ) ^ (grade + 1) *
            scaleG * scaleZ ^ 2 * (radius ^ a * sizeU ^ b * sizeW ^ c) := by positivity
        have square_le : (2 : ℝ) ^ grade * (2 : ℝ) ^ grade ≤
            (4 : ℝ) ^ grade := by
          rw [← mul_pow]
          norm_num
        nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) grade,
          pow_nonneg (show (0:ℝ) ≤ 4 by norm_num) grade]
    _ = _ := by ring

end Grad.NonlinearQuotientBounds
