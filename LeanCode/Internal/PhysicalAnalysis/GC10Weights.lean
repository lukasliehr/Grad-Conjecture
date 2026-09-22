import GC10Basic

noncomputable section

set_option maxHeartbeats 500000

open Set
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Algebra

theorem scaledCellWeight_one_le (L ell : ℝ) (cell : ℤ) :
    1 ≤ scaledCellWeight L ell cell := by
  unfold scaledCellWeight
  exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg ((cell : ℝ) * ell / L)])

theorem sqrt_two_one_le : 1 ≤ Real.sqrt 2 := by
  exact Real.one_le_sqrt.mpr (by norm_num)

theorem originalEnvelope_add_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (first second : ℤ)
    (point : ClosedDisk) :
    originalEnvelope sigma gamma ell (first + second) point.val ≤
      originalEnvelope sigma gamma ell first point.val *
        originalEnvelope sigma gamma ell second point.val := by
  have gammaNonnegative : 0 ≤ gamma := admissible_gamma_nonnegative admissible
  have ellNonnegative : 0 ≤ ell := admissible_ell_nonnegative admissible
  have ellLeOne : ell ≤ 1 := admissible_ell_le_one admissible
  have pointBound : ‖point.val‖ ≤ 1 := point.property
  have gammaLeSigma : gamma ≤ sigma := admissible_gamma_le_sigma admissible
  have ellNormLeOne : ell * ‖point.val‖ ≤ 1 := by
    nlinarith [mul_nonneg ellNonnegative (norm_nonneg point.val),
      mul_le_mul ellLeOne pointBound (norm_nonneg point.val) zero_le_one]
  have rateNonnegative : 0 ≤ sigma - gamma * ell * ‖point.val‖ := by
    nlinarith [mul_le_mul_of_nonneg_left ellNormLeOne gammaNonnegative]
  unfold originalEnvelope
  rw [← Real.exp_add, ← mul_add]
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ rateNonnegative
  push_cast
  exact abs_add_le (first : ℝ) (second : ℝ)

theorem derivative_split_order {grade : ℕ} (index : DerivativeIndex grade)
    (split : DerivativeSplit index) :
    derivativeOrder (lowerDerivativeIndex index split) +
      derivativeOrder (upperDerivativeIndex index split) = derivativeOrder index := by
  simp only [derivativeOrder, lowerDerivativeIndex, upperDerivativeIndex]
  have firstLe : (split.1 : ℕ) ≤ (index.1.1 : ℕ) := Nat.lt_succ_iff.mp split.1.isLt
  have secondLe : (split.2 : ℕ) ≤ (index.1.2 : ℕ) := Nat.lt_succ_iff.mp split.2.isLt
  omega

theorem frequency_scale_bound (L ell : ℝ) (grade : ℕ) (first second : ℤ)
    (index : DerivativeIndex grade) (split : DerivativeSplit index) :
    scaledCellWeight L ell (first + second) ^ (grade - derivativeOrder index) ≤
      (Real.sqrt 2) ^ grade *
        scaledCellWeight L ell first ^
          (grade - derivativeOrder (lowerDerivativeIndex index split)) *
        scaledCellWeight L ell second ^
          (grade - derivativeOrder (upperDerivativeIndex index split)) := by
  let totalRest := grade - derivativeOrder index
  let lowerRest := grade - derivativeOrder (lowerDerivativeIndex index split)
  let upperRest := grade - derivativeOrder (upperDerivativeIndex index split)
  have lowerOrderLe : derivativeOrder (lowerDerivativeIndex index split) ≤
      derivativeOrder index := by
    simp only [derivativeOrder, lowerDerivativeIndex]
    omega
  have upperOrderLe : derivativeOrder (upperDerivativeIndex index split) ≤
      derivativeOrder index := by
    simp only [derivativeOrder, upperDerivativeIndex]
    omega
  have totalRestLeLower : totalRest ≤ lowerRest := by
    dsimp [totalRest, lowerRest]
    omega
  have totalRestLeUpper : totalRest ≤ upperRest := by
    dsimp [totalRest, upperRest]
    omega
  have totalRestLeGrade : totalRest ≤ grade := Nat.sub_le _ _
  have triangle := scaledCellWeight_add_le L ell first second
  have powered := pow_le_pow_left₀ (scaledCellWeight_nonnegative L ell (first + second))
    triangle totalRest
  calc
    scaledCellWeight L ell (first + second) ^ totalRest
        ≤ (Real.sqrt 2 * scaledCellWeight L ell first *
            scaledCellWeight L ell second) ^ totalRest := powered
    _ = (Real.sqrt 2) ^ totalRest * scaledCellWeight L ell first ^ totalRest *
          scaledCellWeight L ell second ^ totalRest := by ring
    _ ≤ (Real.sqrt 2) ^ grade * scaledCellWeight L ell first ^ lowerRest *
          scaledCellWeight L ell second ^ upperRest := by
      have sqrtPower := pow_le_pow_right₀ sqrt_two_one_le totalRestLeGrade
      have firstPower :=
        pow_le_pow_right₀ (scaledCellWeight_one_le L ell first) totalRestLeLower
      have secondPower :=
        pow_le_pow_right₀ (scaledCellWeight_one_le L ell second) totalRestLeUpper
      calc
        (Real.sqrt 2) ^ totalRest * scaledCellWeight L ell first ^ totalRest *
            scaledCellWeight L ell second ^ totalRest =
          (Real.sqrt 2) ^ totalRest *
            (scaledCellWeight L ell first ^ totalRest *
              scaledCellWeight L ell second ^ totalRest) := by ring
        _ ≤ (Real.sqrt 2) ^ grade *
            (scaledCellWeight L ell first ^ totalRest *
              scaledCellWeight L ell second ^ totalRest) :=
          mul_le_mul_of_nonneg_right sqrtPower
            (mul_nonneg (pow_nonneg (scaledCellWeight_nonnegative L ell first) _)
              (pow_nonneg (scaledCellWeight_nonnegative L ell second) _))
        _ ≤ (Real.sqrt 2) ^ grade *
            (scaledCellWeight L ell first ^ lowerRest *
              scaledCellWeight L ell second ^ totalRest) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right firstPower
              (pow_nonneg (scaledCellWeight_nonnegative L ell second) _))
            (pow_nonneg (Real.sqrt_nonneg 2) _)
        _ ≤ (Real.sqrt 2) ^ grade *
            (scaledCellWeight L ell first ^ lowerRest *
              scaledCellWeight L ell second ^ upperRest) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left secondPower
              (pow_nonneg (scaledCellWeight_nonnegative L ell first) _))
            (pow_nonneg (Real.sqrt_nonneg 2) _)
        _ = _ := by ring

theorem coefficientScale_comp_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (first second : ℤ)
    (index : DerivativeIndex grade) (split : DerivativeSplit index) (point : ClosedDisk) :
    coefficientScale L sigma gamma ell grade (first + second) index point ≤
      (Real.sqrt 2) ^ grade *
        coefficientScale L sigma gamma ell grade first
          (lowerDerivativeIndex index split) point *
        coefficientScale L sigma gamma ell grade second
          (upperDerivativeIndex index split) point := by
  unfold coefficientScale
  have envelope := originalEnvelope_add_le admissible first second point
  have frequency := frequency_scale_bound L ell grade first second index split
  calc
    originalEnvelope sigma gamma ell (first + second) point.val *
        scaledCellWeight L ell (first + second) ^ (grade - derivativeOrder index)
        ≤ (originalEnvelope sigma gamma ell first point.val *
            originalEnvelope sigma gamma ell second point.val) *
          ((Real.sqrt 2) ^ grade *
            scaledCellWeight L ell first ^
              (grade - derivativeOrder (lowerDerivativeIndex index split)) *
            scaledCellWeight L ell second ^
              (grade - derivativeOrder (upperDerivativeIndex index split))) :=
      mul_le_mul envelope frequency
        (pow_nonneg (scaledCellWeight_nonnegative L ell _) _)
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = _ := by ring

end Grad.GaugeCoefficients.Algebra
