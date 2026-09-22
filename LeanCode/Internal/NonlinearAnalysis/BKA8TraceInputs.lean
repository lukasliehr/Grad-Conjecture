import BKA7OneHighBound
import SBT4BoundaryAngular

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace

theorem negativeTraceWeight_mul_frequency_eq_positiveTraceWeight
    (parameters : PhaseParameters) (angular cell : ℕ) (mode : ℤ × ℤ) :
    annularFrequency mode.1 mode.2 *
        negativeTraceWeight parameters angular cell mode =
      positiveTraceWeight parameters angular cell mode := by
  let frequency := annularFrequency mode.1 mode.2
  let negative := negativeTraceWeight parameters angular cell mode
  let positive := positiveTraceWeight parameters angular cell mode
  have negativeSq : negative ^ 2 =
      negativeTraceWeightSq parameters angular cell mode := by
    dsimp only [negative, negativeTraceWeight]
    exact Real.sq_sqrt (negativeTraceWeightSq_pos parameters angular cell mode).le
  have positiveSq : positive ^ 2 =
      positiveTraceWeightSq parameters angular cell mode := by
    dsimp only [positive, positiveTraceWeight]
    exact Real.sq_sqrt (positiveTraceWeightSq_pos parameters angular cell mode).le
  have weightSq : positiveTraceWeightSq parameters angular cell mode =
      frequency ^ 2 * negativeTraceWeightSq parameters angular cell mode := by
    unfold positiveTraceWeightSq negativeTraceWeightSq
    dsimp only [frequency]
    have frequencyNe : annularFrequency mode.1 mode.2 ≠ 0 :=
      (annularFrequency_pos mode).ne'
    field_simp
  have squares : (frequency * negative) ^ 2 = positive ^ 2 := by
    rw [mul_pow, negativeSq, positiveSq, weightSq]
  have leftNonneg : 0 ≤ frequency * negative :=
    mul_nonneg (annularFrequency_pos mode).le
      (negativeTraceWeight_pos parameters angular cell mode).le
  have rightNonneg : 0 ≤ positive :=
    (positiveTraceWeight_pos parameters angular cell mode).le
  nlinarith

theorem inverseFrequency_norm_le_one (mode : ℤ × ℤ) :
    ‖((annularFrequency mode.1 mode.2 : ℂ)⁻¹)‖ ≤ 1 := by
  exact boundaryInverseFrequency_bound mode

theorem cellCoefficientRatio_norm_le (mode : ℤ × ℤ) :
    ‖(Complex.I * (mode.2 : ℂ)) /
        (annularFrequency mode.1 mode.2 : ℂ)‖ ≤ 1 := by
  rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast,
    Complex.norm_real, Real.norm_of_nonneg (annularFrequency_pos mode).le,
    div_le_one (annularFrequency_pos mode)]
  unfold annularFrequency
  linarith [abs_nonneg (mode.1 : ℝ)]

/-- The coefficient-preserving inclusion from positive to negative half order. -/
def positiveToNegative {dimension : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ) :
    PositiveTrace parameters angular cell dimension →L[ℂ]
      NegativeTrace parameters angular cell dimension :=
  sequenceMultiplier
    (fun mode => (annularFrequency mode.1 mode.2 : ℂ)⁻¹)
    1 zero_le_one inverseFrequency_norm_le_one

/-- The angular derivative of a positive-half trace, placed in negative half order. -/
def positiveRotationToNegative {dimension : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ) :
    PositiveTrace parameters angular cell dimension →L[ℂ]
      NegativeTrace parameters angular cell dimension :=
  sequenceMultiplier
    (fun mode => (Complex.I * (mode.1 : ℂ)) /
      (annularFrequency mode.1 mode.2 : ℂ))
    1 zero_le_one boundaryAngularRatio_bound

/-- The cell derivative of a positive-half trace, placed in negative half order. -/
def positiveCellToNegative {dimension : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ) :
    PositiveTrace parameters angular cell dimension →L[ℂ]
      NegativeTrace parameters angular cell dimension :=
  sequenceMultiplier
    (fun mode => (Complex.I * (mode.2 : ℂ)) /
      (annularFrequency mode.1 mode.2 : ℂ))
    1 zero_le_one cellCoefficientRatio_norm_le

theorem positiveToNegative_bound {dimension : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ) (field : PositiveTrace parameters angular cell dimension) :
    ‖positiveToNegative parameters angular cell field‖ ≤ ‖field‖ := by
  change ‖sequenceMultiplierValue _ 1 zero_le_one inverseFrequency_norm_le_one field‖ ≤ _
  simpa only [one_mul] using sequenceMultiplierValue_bound
    (fun mode => (annularFrequency mode.1 mode.2 : ℂ)⁻¹)
    1 zero_le_one inverseFrequency_norm_le_one field

theorem positiveRotationToNegative_bound {dimension : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ) (field : PositiveTrace parameters angular cell dimension) :
    ‖positiveRotationToNegative parameters angular cell field‖ ≤ ‖field‖ := by
  change ‖sequenceMultiplierValue _ 1 zero_le_one boundaryAngularRatio_bound field‖ ≤ _
  simpa only [one_mul] using sequenceMultiplierValue_bound
    (fun mode => (Complex.I * (mode.1 : ℂ)) /
      (annularFrequency mode.1 mode.2 : ℂ))
    1 zero_le_one boundaryAngularRatio_bound field

theorem positiveCellToNegative_bound {dimension : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ) (field : PositiveTrace parameters angular cell dimension) :
    ‖positiveCellToNegative parameters angular cell field‖ ≤ ‖field‖ := by
  change ‖sequenceMultiplierValue _ 1 zero_le_one cellCoefficientRatio_norm_le field‖ ≤ _
  simpa only [one_mul] using sequenceMultiplierValue_bound
    (fun mode => (Complex.I * (mode.2 : ℂ)) /
      (annularFrequency mode.1 mode.2 : ℂ))
    1 zero_le_one cellCoefficientRatio_norm_le field

private theorem positiveToNegative_raw {dimension : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ) (field : PositiveTrace parameters angular cell dimension)
    (mode : ℤ × ℤ) :
    positiveToNegative parameters angular cell field mode =
      (annularFrequency mode.1 mode.2 : ℂ)⁻¹ • field mode := by
  have result := sequenceMultiplier_apply
    (fun mode => (annularFrequency mode.1 mode.2 : ℂ)⁻¹)
    1 zero_le_one inverseFrequency_norm_le_one field mode
  unfold positiveToNegative
  with_reducible exact result

private theorem positiveRotationToNegative_raw {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (field : PositiveTrace parameters angular cell dimension) (mode : ℤ × ℤ) :
    positiveRotationToNegative parameters angular cell field mode =
      ((Complex.I * (mode.1 : ℂ)) /
        (annularFrequency mode.1 mode.2 : ℂ)) • field mode := by
  have result := sequenceMultiplier_apply
    (fun mode => (Complex.I * (mode.1 : ℂ)) /
      (annularFrequency mode.1 mode.2 : ℂ))
    1 zero_le_one boundaryAngularRatio_bound field mode
  unfold positiveRotationToNegative
  with_reducible exact result

private theorem positiveCellToNegative_raw {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (field : PositiveTrace parameters angular cell dimension) (mode : ℤ × ℤ) :
    positiveCellToNegative parameters angular cell field mode =
      ((Complex.I * (mode.2 : ℂ)) /
        (annularFrequency mode.1 mode.2 : ℂ)) • field mode := by
  have result := sequenceMultiplier_apply
    (fun mode => (Complex.I * (mode.2 : ℂ)) /
      (annularFrequency mode.1 mode.2 : ℂ))
    1 zero_le_one cellCoefficientRatio_norm_le field mode
  unfold positiveCellToNegative
  with_reducible exact result

theorem positiveToNegative_coefficient {dimension : ℕ} (parameters : PhaseParameters)
    (angular cell : ℕ) (field : PositiveTrace parameters angular cell dimension)
    (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
        (positiveToNegative parameters angular cell field) mode =
      positiveTraceCoefficient parameters angular cell field mode := by
  unfold negativeTraceCoefficient positiveTraceCoefficient
  rw [positiveToNegative_raw]
  simp only [smul_smul]
  congr 1
  have weight := negativeTraceWeight_mul_frequency_eq_positiveTraceWeight
    parameters angular cell mode
  have weightC :
      (annularFrequency mode.1 mode.2 : ℂ) *
          (negativeTraceWeight parameters angular cell mode : ℂ) =
        (positiveTraceWeight parameters angular cell mode : ℂ) := by
    exact_mod_cast weight
  rw [← weightC]
  field_simp [
    (annularFrequency_pos mode).ne',
    (negativeTraceWeight_pos parameters angular cell mode).ne',
    (positiveTraceWeight_pos parameters angular cell mode).ne']

theorem positiveRotationToNegative_coefficient {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (field : PositiveTrace parameters angular cell dimension) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
        (positiveRotationToNegative parameters angular cell field) mode =
      (Complex.I * (mode.1 : ℂ)) •
        positiveTraceCoefficient parameters angular cell field mode := by
  unfold negativeTraceCoefficient positiveTraceCoefficient
  rw [positiveRotationToNegative_raw]
  simp only [smul_smul]
  congr 1
  have weight := negativeTraceWeight_mul_frequency_eq_positiveTraceWeight
    parameters angular cell mode
  have weightC :
      (annularFrequency mode.1 mode.2 : ℂ) *
          (negativeTraceWeight parameters angular cell mode : ℂ) =
        (positiveTraceWeight parameters angular cell mode : ℂ) := by
    exact_mod_cast weight
  rw [← weightC]
  field_simp [
    (annularFrequency_pos mode).ne',
    (negativeTraceWeight_pos parameters angular cell mode).ne',
    (positiveTraceWeight_pos parameters angular cell mode).ne']

theorem positiveCellToNegative_coefficient {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (field : PositiveTrace parameters angular cell dimension) (mode : ℤ × ℤ) :
    negativeTraceCoefficient parameters angular cell
        (positiveCellToNegative parameters angular cell field) mode =
      (Complex.I * (mode.2 : ℂ)) •
        positiveTraceCoefficient parameters angular cell field mode := by
  unfold negativeTraceCoefficient positiveTraceCoefficient
  rw [positiveCellToNegative_raw]
  simp only [smul_smul]
  congr 1
  have weight := negativeTraceWeight_mul_frequency_eq_positiveTraceWeight
    parameters angular cell mode
  have weightC :
      (annularFrequency mode.1 mode.2 : ℂ) *
          (negativeTraceWeight parameters angular cell mode : ℂ) =
        (positiveTraceWeight parameters angular cell mode : ℂ) := by
    exact_mod_cast weight
  rw [← weightC]
  field_simp [
    (annularFrequency_pos mode).ne',
    (negativeTraceWeight_pos parameters angular cell mode).ne',
    (positiveTraceWeight_pos parameters angular cell mode).ne']

end Grad.BoundaryKernelAction
