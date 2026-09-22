import COR12TorusFubini

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Grad.COR12Extension

open Grad.ClosedJets
open Grad.DiskExtension.Operator
open Grad.FourierGrade

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def torusSmoothCoefficient {dimension : ℕ}
    (field : TorusSmoothField dimension) (mode : FourierMode) :
    ComplexEuclidean dimension :=
  UnitAddTorus.mFourierCoeff (torusSmoothNormalizedValue field) (modeVector mode)

theorem euclideanContinuousCoefficient_sq_summable {dimension : ℕ}
    (field : C(ProductTorus, ComplexEuclidean dimension)) :
    Summable (fun mode : FourierMode =>
      ‖UnitAddTorus.mFourierCoeff field (modeVector mode)‖ ^ 2) := by
  have coordinateSums := summable_sum (s := Finset.univ)
    (fun coordinate _ =>
      euclidean_component_sq_summable
        (ContinuousMap.toLp 2 volume ℂ field) coordinate)
  apply coordinateSums.congr
  intro mode
  rw [← PiLp.norm_sq_eq_of_L2]
  rw [euclideanTorusCoefficient_continuousToLp]

theorem torusSmoothDerivative_coefficient_norm_sq {dimension : ℕ}
    (field : TorusSmoothField dimension) (index : DiskCellMultiIndex)
    (mode : FourierMode) :
    ‖UnitAddTorus.mFourierCoeff
        (normalizedMixedDerivative field (diskCellMultiIndexWord index))
        (modeVector mode)‖ ^ 2 =
      derivativeMultiplier index mode * ‖torusSmoothCoefficient field mode‖ ^ 2 := by
  rw [normalizedDiskCellDerivative_coefficient, norm_smul, mul_pow,
    mixedFrequencyFactor_norm_sq]
  rfl

theorem torusSmoothDerivative_coefficient_summable {dimension : ℕ}
    (field : TorusSmoothField dimension) (index : DiskCellMultiIndex) :
    Summable (fun mode : FourierMode =>
      derivativeMultiplier index mode * ‖torusSmoothCoefficient field mode‖ ^ 2) := by
  apply (euclideanContinuousCoefficient_sq_summable
    (normalizedMixedDerivative field (diskCellMultiIndexWord index))).congr
  intro mode
  exact torusSmoothDerivative_coefficient_norm_sq field index mode

theorem torusSmoothDerivative_parseval {dimension : ℕ}
    (field : TorusSmoothField dimension) (index : DiskCellMultiIndex) :
    (∫ point : ProductTorus,
      ‖normalizedMixedDerivative field (diskCellMultiIndexWord index) point‖ ^ 2) =
      ∑' mode : FourierMode,
        derivativeMultiplier index mode * ‖torusSmoothCoefficient field mode‖ ^ 2 := by
  exact (euclidean_continuous_torus_parseval
    (normalizedMixedDerivative field (diskCellMultiIndexWord index))).trans
      (tsum_congr (torusSmoothDerivative_coefficient_norm_sq field index))

theorem torusSmoothDerivativeWeight_summable {dimension : ℕ}
    (field : TorusSmoothField dimension) (grade : ℕ) :
    Summable (fun mode : FourierMode =>
      derivativeWeight grade mode * ‖torusSmoothCoefficient field mode‖ ^ 2) := by
  have indices := summable_sum (s := fourierMultiIndices grade)
    (fun index _ => torusSmoothDerivative_coefficient_summable field index)
  simpa only [derivativeWeight, Finset.sum_mul] using indices

theorem torusSmoothGrade_summable {dimension : ℕ}
    (field : TorusSmoothField dimension) (grade : ℕ) :
    Summable (fun mode : FourierMode =>
      frequencyWeight mode ^ (2 * grade) * ‖torusSmoothCoefficient field mode‖ ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun mode => gradeSequenceTerm_nonneg grade (torusSmoothCoefficient field) mode)
    _ ((torusSmoothDerivativeWeight_summable field grade).mul_left ((4 : ℝ) ^ grade))
  intro mode
  calc
    frequencyWeight mode ^ (2 * grade) * ‖torusSmoothCoefficient field mode‖ ^ 2 ≤
        ((4 : ℝ) ^ grade * derivativeWeight grade mode) *
          ‖torusSmoothCoefficient field mode‖ ^ 2 :=
      mul_le_mul_of_nonneg_right
        (gradeWeight_le_four_pow_mul_derivativeWeight grade mode) (sq_nonneg _)
    _ = (4 : ℝ) ^ grade *
        (derivativeWeight grade mode * ‖torusSmoothCoefficient field mode‖ ^ 2) := by ring

/-- Fourier analysis of any P09 smooth field lies in every original-width
integer Fourier grade, with no extra regularity premise. -/
def torusSmoothFourierCore {dimension : ℕ}
    (field : TorusSmoothField dimension) : JCore (ComplexEuclidean dimension) := by
  refine ⟨torusSmoothCoefficient field, fun grade => ?_⟩
  apply memℓp_gen
  norm_num
  apply (torusSmoothGrade_summable field grade).congr
  intro mode
  rw [norm_smul, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (frequencyWeight_pos mode)]
  ring

def normalizedTorusDerivativeEnergy {dimension : ℕ} (grade : ℕ)
    (field : TorusSmoothField dimension) : ℝ :=
  ∑ index ∈ fourierMultiIndices grade,
    ∫ point : ProductTorus,
      ‖normalizedMixedDerivative field (diskCellMultiIndexWord index) point‖ ^ 2

theorem normalizedTorusDerivativeEnergy_eq_sequenceEnergy {dimension : ℕ}
    (field : TorusSmoothField dimension) (grade : ℕ) :
    normalizedTorusDerivativeEnergy grade field =
      derivativeSequenceEnergy grade (torusSmoothCoefficient field) := by
  calc
    normalizedTorusDerivativeEnergy grade field =
        ∑ index ∈ fourierMultiIndices grade,
          ∑' mode : FourierMode,
            derivativeMultiplier index mode * ‖torusSmoothCoefficient field mode‖ ^ 2 := by
      exact Finset.sum_congr rfl (fun index _ => torusSmoothDerivative_parseval field index)
    _ = ∑' mode : FourierMode,
        ∑ index ∈ fourierMultiIndices grade,
          derivativeMultiplier index mode * ‖torusSmoothCoefficient field mode‖ ^ 2 :=
      (Summable.tsum_finsetSum
        (fun index _ => torusSmoothDerivative_coefficient_summable field index)).symm
    _ = derivativeSequenceEnergy grade (torusSmoothCoefficient field) := by
      simp only [derivativeSequenceEnergy, derivativeWeight, Finset.sum_mul]

theorem torusSmoothFourierCore_norm_sq {dimension : ℕ}
    (field : TorusSmoothField dimension) (grade : ℕ) :
    ‖coreToGrade grade (torusSmoothFourierCore field)‖ ^ 2 =
      gradeSequenceEnergy grade (torusSmoothCoefficient field) := by
  rw [norm_sq_eq_weighted_tsum]
  simp only [coreToGrade_coefficient]
  rfl

/-- Both exact P15 constants for arbitrary smooth P09 fields. -/
theorem torusSmoothFourierCore_energy_comparison {dimension : ℕ}
    (field : TorusSmoothField dimension) (grade : ℕ) :
    ((4 : ℝ) ^ grade)⁻¹ * ‖coreToGrade grade (torusSmoothFourierCore field)‖ ^ 2 ≤
        normalizedTorusDerivativeEnergy grade field ∧
      normalizedTorusDerivativeEnergy grade field ≤
        (Nat.choose (grade + 3) 3 : ℝ) *
          ‖coreToGrade grade (torusSmoothFourierCore field)‖ ^ 2 := by
  rw [normalizedTorusDerivativeEnergy_eq_sequenceEnergy,
    torusSmoothFourierCore_norm_sq]
  exact ⟨inverse_four_pow_mul_gradeSequenceEnergy_le_derivativeSequenceEnergy
      grade (torusSmoothCoefficient field) (torusSmoothGrade_summable field grade),
    derivativeSequenceEnergy_le_choose_mul_gradeSequenceEnergy
      grade (torusSmoothCoefficient field) (torusSmoothGrade_summable field grade)⟩

end Grad.COR12Extension
