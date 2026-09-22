import GC14SeedLaurent
import GC14SeedMatrixFormula

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Physical.Frame

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Neumann.Regularity

def seedAmplitudeConstant (radius : ℝ) : ℝ := 2 * (1 + radius) ^ 2

theorem seedLaurentAmplitude_bound {radius sign alpha delta parameter : ℝ}
    (radiusNonnegative : 0 ≤ radius) (signSmall : |sign| ≤ 1)
    (alphaSmall : |alpha| ≤ radius) (deltaSmall : |delta| ≤ radius)
    (parameterSmall : |parameter| ≤ radius) (mode : Fin 5) :
    ‖seedLaurentAmplitude sign alpha delta parameter mode‖ ≤ seedAmplitudeConstant radius := by
  have first : |sign| * |alpha| ≤ radius := by
    calc
      _ ≤ 1 * radius := mul_le_mul signSmall alphaSmall (abs_nonneg alpha) zero_le_one
      _ = _ := one_mul _
  have second : |sign| * |delta| ≤ radius := by
    calc
      _ ≤ 1 * radius := mul_le_mul signSmall deltaSmall (abs_nonneg delta) zero_le_one
      _ = _ := one_mul _
  have third : |sign| * |delta| * |parameter| ≤ radius ^ 2 := by
    exact (mul_le_mul second parameterSmall (abs_nonneg parameter) radiusNonnegative).trans_eq
      (pow_two radius).symm
  fin_cases mode <;>
    norm_num [seedLaurentAmplitude, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      seedAmplitudeConstant]
  all_goals nlinarith [sq_nonneg radius]

def seedGeneratorConstant (sigma radius : ℝ) (grade : ℕ) : ℝ :=
  (Fintype.card (DerivativeIndex grade) : ℝ) *
    (∑ mode : Fin 5, Real.exp (sigma * |(seedLaurentCell mode : ℝ)|) *
      cellFrequency (seedLaurentCell mode) ^ grade) * seedAmplitudeConstant radius

theorem seedGeneratorConstant_nonnegative (sigma radius : ℝ) (grade : ℕ) :
    0 ≤ seedGeneratorConstant sigma radius grade := by
  unfold seedGeneratorConstant seedAmplitudeConstant
  apply mul_nonneg
  · apply mul_nonneg (Nat.cast_nonneg _)
    exact Finset.sum_nonneg fun mode _ => mul_nonneg (Real.exp_pos _).le
      (pow_nonneg (cellFrequency_pos _).le _)
  · positivity

theorem seedAngleGenerator_norm_le {L sigma gamma ell radius sign alpha delta parameter : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    (radiusNonnegative : 0 ≤ radius) (signSmall : |sign| ≤ 1)
    (alphaSmall : |alpha| ≤ radius) (deltaSmall : |delta| ≤ radius)
    (parameterSmall : |parameter| ≤ radius) :
    ‖seedAngleGenerator L sigma gamma ell grade sign alpha delta parameter‖ ≤
      seedGeneratorConstant sigma radius grade := by
  have each (mode : Fin 5) :
      ‖seedLaurentAmplitude sign alpha delta parameter mode •
        ContinuousLinearMap.id ℂ (ComplexEuclidean 1)‖ ≤ seedAmplitudeConstant radius := by
    calc
      _ ≤ ‖seedLaurentAmplitude sign alpha delta parameter mode‖ *
          ‖ContinuousLinearMap.id ℂ (ComplexEuclidean 1)‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ ‖seedLaurentAmplitude sign alpha delta parameter mode‖ * 1 :=
        mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
      _ ≤ _ := by
        rw [mul_one]
        exact seedLaurentAmplitude_bound radiusNonnegative signSmall alphaSmall deltaSmall parameterSmall mode
  unfold seedAngleGenerator
  calc
    _ ≤ ∑ mode : Fin 5, ‖seedConstantCell L sigma gamma ell grade (seedLaurentCell mode)
        (seedLaurentAmplitude sign alpha delta parameter mode •
          ContinuousLinearMap.id ℂ (ComplexEuclidean 1))‖ := norm_sum_le _ _
    _ ≤ ∑ mode : Fin 5, (Fintype.card (DerivativeIndex grade) : ℝ) *
        (Real.exp (sigma * |(seedLaurentCell mode : ℝ)|) *
          cellFrequency (seedLaurentCell mode) ^ grade * seedAmplitudeConstant radius) := by
      apply Finset.sum_le_sum
      intro mode _
      exact (seedConstantCell_norm_le admissible (seedLaurentCell mode) _).trans
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (each mode)
          (mul_nonneg (Real.exp_pos _).le (pow_nonneg (cellFrequency_pos _).le _)))
            (Nat.cast_nonneg _))
    _ = _ := by
      unfold seedGeneratorConstant
      rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring

theorem seedGradedIdentity_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    ‖gradedIdentityCoefficient L sigma gamma ell grade 1‖ ≤ Fintype.card (DerivativeIndex grade) := by
  have same : gradedIdentityCoefficient L sigma gamma ell grade 1 =
      seedConstantCell L sigma gamma ell grade 0
        (ContinuousLinearMap.id ℂ (ComplexEuclidean 1)) := by
    apply Subtype.ext
    change weightedSingle L sigma gamma ell grade 0 (identitySmoothOperatorJet 1) =
      weightedSingle L sigma gamma ell grade 0
        (seedConstantJet (ContinuousLinearMap.id ℂ (ComplexEuclidean 1)))
    have jets : identitySmoothOperatorJet 1 =
        seedConstantJet (ContinuousLinearMap.id ℂ (ComplexEuclidean 1)) := by rfl
    exact congrArg (weightedSingle L sigma gamma ell grade 0) jets
  rw [same]
  have bound := seedConstantCell_norm_le admissible (grade := grade) 0
    (ContinuousLinearMap.id ℂ (ComplexEuclidean 1))
  have zeroFrequency : cellFrequency 0 = 1 := by norm_num [cellFrequency_formula]
  have identityNorm : ‖ContinuousLinearMap.id ℂ (ComplexEuclidean 1)‖ = 1 :=
    ContinuousLinearMap.norm_id
  simpa only [Int.cast_zero, abs_zero, mul_zero, Real.exp_zero, zeroFrequency,
    one_pow, one_mul, identityNorm, mul_one] using bound

def seedExponentialConstant (sigma radius : ℝ) (grade : ℕ) : ℝ :=
  (Fintype.card (DerivativeIndex grade) : ℝ) *
    Real.exp (gradeProductConstant grade * seedGeneratorConstant sigma radius grade)

theorem seedAngleExponential_norm_le {L sigma gamma ell radius sign alpha delta parameter : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    (radiusNonnegative : 0 ≤ radius) (signSmall : |sign| ≤ 1)
    (alphaSmall : |alpha| ≤ radius) (deltaSmall : |delta| ≤ radius)
    (parameterSmall : |parameter| ≤ radius) :
    ‖seedAngleExponential admissible grade sign alpha delta parameter‖ ≤
      seedExponentialConstant sigma radius grade := by
  exact (seedCoefficientExponential_norm_le admissible _).trans
    (mul_le_mul (seedGradedIdentity_norm_le admissible grade)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
        (seedAngleGenerator_norm_le admissible grade radiusNonnegative signSmall alphaSmall deltaSmall parameterSmall)
        (seedProductConstant_nonnegative grade))) (Real.exp_pos _).le (Nat.cast_nonneg _))

end Grad.GaugeCoefficients.Physical.Frame
