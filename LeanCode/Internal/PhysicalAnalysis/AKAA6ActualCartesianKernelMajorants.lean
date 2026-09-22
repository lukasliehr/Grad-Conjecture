import AKAA5ActualConjugatedCoefficientJet

noncomputable section

set_option maxHeartbeats 1200000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnalyticWeights.Higher

def startupDerivativeMajorant {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (index : DerivativeIndex grade) (shift : ℤ) : ℝ :=
  ∑ split : DerivativeSplit index, (splitMultiplicity index split : ℝ) *
    apRatioConstant L sigma gamma (derivativeOrder (lowerDerivativeIndex index split)) *
      ‖weightedDerivative coefficient shift (upperDerivativeIndex index split)‖

def startupDerivativeConstant {grade : ℕ} (L sigma gamma : ℝ)
    (index : DerivativeIndex grade) : ℝ :=
  ∑ split : DerivativeSplit index, (splitMultiplicity index split : ℝ) *
    apRatioConstant L sigma gamma (derivativeOrder (lowerDerivativeIndex index split))

theorem startupAllocatedCoefficient_unreserve {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (rank : ℕ) (word : Fin rank → Fin 2) (index : DerivativeIndex grade)
    (input shift : ℤ) (point : ClosedDisk) :
    (apRatioDerivative sigma gamma ell rank word input shift point : ℂ) •
      coefficientDerivative coefficient shift index point =
        ((scaledCellWeight L ell input ^ (rank - 1) : ℝ) : ℂ) •
          startupAllocatedCoefficient coefficient rank word index input shift point := by
  have nonzero : (scaledCellWeight L ell input ^ (rank - 1) : ℝ) ≠ 0 :=
    (pow_pos (lt_of_lt_of_le zero_lt_one (scaledCellWeight_one_le L ell input)) _).ne'
  change _ = ((scaledCellWeight L ell input ^ (rank - 1) : ℝ) : ℂ) •
    (((apRatioDerivative sigma gamma ell rank word input shift point /
      scaledCellWeight L ell input ^ (rank - 1) : ℝ) : ℂ) •
      coefficientDerivative coefficient shift index point)
  rw [smul_smul, ← Complex.ofReal_mul]
  congr 2
  field_simp

theorem startupDerivativeMajorant_nonnegative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (index : DerivativeIndex grade) (shift : ℤ) :
    0 ≤ startupDerivativeMajorant coefficient index shift :=
  Finset.sum_nonneg fun split _ => mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (apRatioConstant_nonnegative admissible _))
    (norm_nonneg (weightedDerivative coefficient shift (upperDerivativeIndex index split)))

theorem startupConjugatedCoefficientJet_derivative_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (input shift : ℤ)
    (index : DerivativeIndex grade) (point : ClosedDisk) :
    ‖smoothOperatorDerivative (startupConjugatedCoefficientJet admissible family coherent input shift)
      (derivativeMultiIndex index) point‖ ≤
      startupDerivativeMajorant (family grade) index shift *
        scaledCellWeight L ell input ^ (derivativeOrder index - 1) := by
  rw [startupConjugatedCoefficientJet_derivative, startupDerivativeMajorant, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro split _
  let phaseRank := derivativeOrder (lowerDerivativeIndex index split)
  have allocation : phaseRank + derivativeOrder (upperDerivativeIndex index split) ≤ grade :=
    (derivative_split_order index split).le.trans index.property
  have phaseOrder : phaseRank ≤ derivativeOrder index := by
    have := derivative_split_order index split
    dsimp [phaseRank]
    omega
  have scalarNonnegative := apRatioConstant_nonnegative admissible phaseRank
  rw [norm_smul, Complex.norm_natCast]
  simp only [mul_assoc]
  apply mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg (splitMultiplicity index split))
  erw [startupAllocatedCoefficient_unreserve]
  rw [norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (pow_nonneg (scaledCellWeight_nonnegative L ell input) _)]
  calc
    _ ≤ scaledCellWeight L ell input ^ (phaseRank - 1) *
        (apRatioConstant L sigma gamma phaseRank *
          ‖weightedDerivative (family grade) shift (upperDerivativeIndex index split)‖) :=
      mul_le_mul_of_nonneg_left (startupAllocatedCoefficient_point_bound admissible (family grade)
        phaseRank _ _ allocation input shift point)
          (pow_nonneg (scaledCellWeight_nonnegative L ell input) _)
    _ ≤ scaledCellWeight L ell input ^ (derivativeOrder index - 1) *
        (apRatioConstant L sigma gamma phaseRank *
          ‖weightedDerivative (family grade) shift (upperDerivativeIndex index split)‖) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (scaledCellWeight_one_le L ell input)
        (by omega)) (mul_nonneg scalarNonnegative
          (norm_nonneg (weightedDerivative (family grade) shift (upperDerivativeIndex index split))))
    _ = _ := by ring

theorem startupDerivativeMajorant_summable {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (index : DerivativeIndex grade) : Summable (startupDerivativeMajorant coefficient index) := by
  apply summable_sum
  intro split _
  exact (coordinate_norm_summable coefficient.val (upperDerivativeIndex index split)).mul_left _

theorem startupDerivativeMajorant_sum_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell)
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (index : DerivativeIndex grade) :
    (∑' shift : ℤ, startupDerivativeMajorant coefficient index shift) ≤
      startupDerivativeConstant L sigma gamma index * ‖coefficient‖ := by
  rw [startupDerivativeConstant, Finset.sum_mul]
  change (∑' shift : ℤ, ∑ split : DerivativeSplit index,
    (splitMultiplicity index split : ℝ) *
      apRatioConstant L sigma gamma (derivativeOrder (lowerDerivativeIndex index split)) *
        ‖weightedDerivative coefficient shift (upperDerivativeIndex index split)‖) ≤ _
  have each (split : DerivativeSplit index) : Summable (fun shift : ℤ =>
      (splitMultiplicity index split : ℝ) *
        apRatioConstant L sigma gamma (derivativeOrder (lowerDerivativeIndex index split)) *
          ‖weightedDerivative coefficient shift (upperDerivativeIndex index split)‖) :=
    (coordinate_norm_summable coefficient.val (upperDerivativeIndex index split)).mul_left _
  rw [(hasSum_sum (s := Finset.univ) (fun split _ => (each split).hasSum)).tsum_eq]
  apply Finset.sum_le_sum
  intro split _
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left (coordinate_norm_sum_le coefficient.val (upperDerivativeIndex index split))
    (mul_nonneg (Nat.cast_nonneg _) (apRatioConstant_nonnegative admissible _))

end Grad.GaugeCoefficients.Physical.RadialLedger
