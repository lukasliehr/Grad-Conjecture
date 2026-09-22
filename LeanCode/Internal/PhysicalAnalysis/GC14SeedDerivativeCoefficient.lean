import GC14SeedDeviation
import GC14SeedSpatialConstancy

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Physical.Frame

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity

def seedScaledFrequency (L ell : ℝ) (cell : ℤ) : ℂ :=
  ((ell / L : ℝ) : ℂ) * (Complex.I * (cell : ℂ))

theorem seedScaledFrequency_norm_le (L ell : ℝ) (cell : ℤ) :
    ‖seedScaledFrequency L ell cell‖ ≤ scaledCellWeight L ell cell := by
  have normFormula : ‖seedScaledFrequency L ell cell‖ = |(cell : ℝ) * ell / L| := by
    unfold seedScaledFrequency
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      Complex.norm_intCast, one_mul]
    rw [← abs_mul]
    congr 1
    ring
  rw [normFormula]
  unfold scaledCellWeight
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by linarith)

def seedDerivativeFamily (L ell rho alpha delta parameter : ℝ) (cell : ℤ) : SmoothOperatorJet 2 2 :=
  seedConstantJet (scaledSeedDerivativeCell L ell rho alpha delta parameter cell)

theorem seedDerivativeFamily_weighted {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade : ℕ}
    (rho alpha delta parameter : ℝ) (cell : ℤ) (index : DerivativeIndex grade)
    (zeroOrder : derivativeOrder index = 0) :
    weightedSmoothDerivative L sigma gamma ell grade cell
        (seedDerivativeFamily L ell rho alpha delta parameter cell) index =
      (seedScaledFrequency L ell cell / (scaledCellWeight L ell cell : ℂ)) •
        weightedDerivative (seedMatrixDeviationCoefficient admissible (grade + 1) rho alpha delta parameter)
          cell (Grad.GaugeCoefficients.Neumann.Regularity.zeroDerivativeIndexAt (grade + 1)) := by
  apply ContinuousMap.ext
  intro point
  change (coefficientScale L sigma gamma ell grade cell index point : ℂ) •
    smoothOperatorDerivative (seedConstantJet (scaledSeedDerivativeCell L ell rho alpha delta parameter cell))
      (derivativeMultiIndex index) point =
    (seedScaledFrequency L ell cell / (scaledCellWeight L ell cell : ℂ)) •
      weightedDerivative (seedMatrixDeviationCoefficient admissible (grade + 1) rho alpha delta parameter)
        cell (Grad.GaugeCoefficients.Neumann.Regularity.zeroDerivativeIndexAt (grade + 1)) point
  rw [seedConstantJet_derivative]
  unfold seedConstantDerivative
  change (coefficientScale L sigma gamma ell grade cell index point : ℂ) •
    (if derivativeOrder index = 0 then seedConstantValue _ else 0) point = _
  rw [if_pos zeroOrder, weighted_derivative_literal,
    seedMatrixDeviation_cell admissible (grade + 1)]
  change (coefficientScale L sigma gamma ell grade cell index point : ℂ) •
    (scaledSeedDerivativeCell L ell rho alpha delta parameter cell) = _
  unfold coefficientScale
  rw [zeroOrder, derivativeOrder_zeroDerivativeIndexAt]
  simp only [Nat.sub_zero, pow_succ]
  unfold scaledSeedDerivativeCell seedScaledFrequency
  apply ContinuousLinearMap.ext
  intro vector
  apply PiLp.ext
  intro coordinate
  simp only [smul_apply, PiLp.smul_apply, smul_eq_mul]
  have nonzero : (scaledCellWeight L ell cell : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le zero_lt_one (scaledCellWeight_one_le L ell cell)).ne'
  push_cast
  field_simp

theorem seedDerivativeFamily_weighted_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade : ℕ}
    (rho alpha delta parameter : ℝ) (cell : ℤ) (index : DerivativeIndex grade) :
    ‖weightedSmoothDerivative L sigma gamma ell grade cell
        (seedDerivativeFamily L ell rho alpha delta parameter cell) index‖ ≤
      ‖weightedDerivative (seedMatrixDeviationCoefficient admissible (grade + 1) rho alpha delta parameter)
        cell (Grad.GaugeCoefficients.Neumann.Regularity.zeroDerivativeIndexAt (grade + 1))‖ := by
  by_cases zeroOrder : derivativeOrder index = 0
  · rw [seedDerivativeFamily_weighted admissible rho alpha delta parameter cell index zeroOrder]
    have scalarBound : ‖seedScaledFrequency L ell cell / (scaledCellWeight L ell cell : ℂ)‖ ≤ 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (scaledCellWeight_nonnegative L ell cell)]
      exact (div_le_one (lt_of_lt_of_le zero_lt_one (scaledCellWeight_one_le L ell cell))).mpr
        (seedScaledFrequency_norm_le L ell cell)
    apply (ContinuousMap.norm_le _ (norm_nonneg
      (weightedDerivative (seedMatrixDeviationCoefficient admissible (grade + 1) rho alpha delta parameter)
        cell (Grad.GaugeCoefficients.Neumann.Regularity.zeroDerivativeIndexAt (grade + 1))))).2
    intro point
    change ‖(seedScaledFrequency L ell cell / (scaledCellWeight L ell cell : ℂ)) •
      weightedDerivative (seedMatrixDeviationCoefficient admissible (grade + 1) rho alpha delta parameter)
        cell (Grad.GaugeCoefficients.Neumann.Regularity.zeroDerivativeIndexAt (grade + 1)) point‖ ≤ _
    rw [norm_smul]
    exact (mul_le_mul scalarBound (ContinuousMap.norm_coe_le_norm _ point) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul _)
  · have zeroValue : weightedSmoothDerivative L sigma gamma ell grade cell
        (seedDerivativeFamily L ell rho alpha delta parameter cell) index = 0 := by
      apply ContinuousMap.ext
      intro point
      change (coefficientScale L sigma gamma ell grade cell index point : ℂ) •
        smoothOperatorDerivative (seedConstantJet _) (derivativeMultiIndex index) point = 0
      rw [seedConstantJet_derivative]
      unfold seedConstantDerivative
      change (coefficientScale L sigma gamma ell grade cell index point : ℂ) •
        (if derivativeOrder index = 0 then seedConstantValue _ else 0) point = 0
      rw [if_neg zeroOrder]
      apply ContinuousLinearMap.ext
      intro vector
      simp
    apply (ContinuousMap.norm_le _ (norm_nonneg
      (weightedDerivative (seedMatrixDeviationCoefficient admissible (grade + 1) rho alpha delta parameter)
        cell (Grad.GaugeCoefficients.Neumann.Regularity.zeroDerivativeIndexAt (grade + 1))))).2
    intro point
    rw [zeroValue]
    change ‖(0 : OperatorValue 2 2)‖ ≤ _
    rw [norm_zero]
    exact norm_nonneg _

theorem seedDerivativeFamily_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (rho alpha delta parameter : ℝ) :
    familySummable L sigma gamma ell grade (seedDerivativeFamily L ell rho alpha delta parameter) := by
  intro index
  exact Summable.of_nonneg_of_le (fun cell => norm_nonneg
    (weightedSmoothDerivative L sigma gamma ell grade cell
      (seedDerivativeFamily L ell rho alpha delta parameter cell) index))
    (fun cell => seedDerivativeFamily_weighted_norm_le admissible rho alpha delta parameter cell index)
    (coordinate_norm_summable
      (seedMatrixDeviationCoefficient admissible (grade + 1) rho alpha delta parameter).val
      (Grad.GaugeCoefficients.Neumann.Regularity.zeroDerivativeIndexAt (grade + 1)))

def seedDerivativeCoefficient {L sigma gamma ell : ℝ}
    (_admissible : Admissible L sigma gamma ell) (grade : ℕ) (rho alpha delta parameter : ℝ) :
    Coefficient L sigma gamma ell grade 2 2 :=
  familyCoefficient L sigma gamma ell grade (seedDerivativeFamily L ell rho alpha delta parameter)

theorem seedDerivativeCoefficient_derivative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (rho alpha delta parameter : ℝ)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative (seedDerivativeCoefficient admissible grade rho alpha delta parameter)
        cell index point =
      if derivativeOrder index = 0 then scaledSeedDerivativeCell L ell rho alpha delta parameter cell else 0 := by
  rw [seedDerivativeCoefficient,
    familyCoefficient_derivative _ (seedDerivativeFamily_summable admissible grade rho alpha delta parameter)]
  unfold seedDerivativeFamily
  rw [seedConstantJet_derivative]
  unfold seedConstantDerivative
  change (if derivativeOrder index = 0 then seedConstantValue _ else 0) point = _
  split_ifs <;> rfl

theorem seedDerivativeCoefficient_norm_le_high {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (rho alpha delta parameter : ℝ) :
    ‖seedDerivativeCoefficient admissible grade rho alpha delta parameter‖ ≤
      (Fintype.card (DerivativeIndex grade) : ℝ) *
        ‖seedMatrixDeviationCoefficient admissible (grade + 1) rho alpha delta parameter‖ := by
  rw [seedDerivativeCoefficient,
    familyCoefficient_norm_formula _ (seedDerivativeFamily_summable admissible grade rho alpha delta parameter)]
  calc
    _ ≤ ∑ _index : DerivativeIndex grade,
        ‖seedMatrixDeviationCoefficient admissible (grade + 1) rho alpha delta parameter‖ := by
      apply Finset.sum_le_sum
      intro index _
      exact ((seedDerivativeFamily_summable admissible grade rho alpha delta parameter index).tsum_le_tsum
        (fun cell => seedDerivativeFamily_weighted_norm_le admissible rho alpha delta parameter cell index)
        (coordinate_norm_summable
          (seedMatrixDeviationCoefficient admissible (grade + 1) rho alpha delta parameter).val
          (Grad.GaugeCoefficients.Neumann.Regularity.zeroDerivativeIndexAt (grade + 1)))).trans
        (coordinate_norm_sum_le
          (seedMatrixDeviationCoefficient admissible (grade + 1) rho alpha delta parameter).val
          (Grad.GaugeCoefficients.Neumann.Regularity.zeroDerivativeIndexAt (grade + 1)))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

def seedDerivativeConstant (sigma radius : ℝ) (grade : ℕ) : ℝ :=
  (Fintype.card (DerivativeIndex grade) : ℝ) * seedDeviationConstant sigma radius (grade + 1)

theorem seedDerivativeConstant_nonnegative (sigma radius : ℝ) (grade : ℕ) :
    0 ≤ seedDerivativeConstant sigma radius grade :=
  mul_nonneg (Nat.cast_nonneg _) (seedDeviationConstant_nonnegative sigma radius (grade + 1))

theorem seedDerivativeCoefficient_norm_le {L sigma gamma ell radius rho alpha delta parameter : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    (radiusNonnegative : 0 ≤ radius) (rhoSmall : |rho| ≤ 1)
    (alphaSmall : |alpha| ≤ radius) (deltaSmall : |delta| ≤ radius)
    (parameterSmall : |parameter| ≤ radius) :
    ‖seedDerivativeCoefficient admissible grade rho alpha delta parameter‖ ≤
      seedDerivativeConstant sigma radius grade * |rho| := by
  exact (seedDerivativeCoefficient_norm_le_high admissible grade rho alpha delta parameter).trans
    ((mul_le_mul_of_nonneg_left
      (seedMatrixDeviation_norm_le admissible (grade + 1) radiusNonnegative rhoSmall alphaSmall deltaSmall parameterSmall)
      (Nat.cast_nonneg (Fintype.card (DerivativeIndex grade)))).trans_eq (by
        unfold seedDerivativeConstant
        ring))

end Grad.GaugeCoefficients.Physical.Frame
