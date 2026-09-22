import GQC20ProductDerivativeL2

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope
open Grad.AnalyticWeights.Calculus Grad.AnalyticWeights.Higher

def phaseProductIndexConstant {grade : ℕ} (L gamma : ℝ) (index : DerivativeIndex grade) : ℝ :=
  ∑ split : DerivativeSplit index, (splitMultiplicity index split : ℝ) *
    phaseDirectionalConstant L gamma (derivativeOrder (lowerDerivativeIndex index split))

theorem phaseProductIndexConstant_nonnegative {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade : ℕ} (index : DerivativeIndex grade) : 0 ≤ phaseProductIndexConstant L gamma index :=
  Finset.sum_nonneg (fun _split _ => mul_nonneg (Nat.cast_nonneg _) (phaseDirectionalConstant_nonnegative admissible _))

theorem phaseProduct_derivative_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension grade : ℕ} (cell : ℤ) (coordinate : Fin 2) (field : ClosedJet dimension) (index : DerivativeIndex grade) :
    scaledCellWeight L ell cell ^ (grade - derivativeOrder index) *
      ‖closedDerivativeL2 (derivativeMultiIndex index)
        (apProductJet (apScalarOperatorJet dimension (phaseDirectional sigma gamma ell cell coordinate)
          (phaseDirectional_smooth sigma gamma ell cell coordinate)) (apWeightedJet sigma gamma ell cell field))‖ ≤
      phaseProductIndexConstant L gamma index * ‖apRowLinear (grade := grade + 1) L sigma gamma ell cell field‖ := by
  apply (mul_le_mul_of_nonneg_left (apProductJet_derivativeL2_bound _ _ index)
    (pow_nonneg (scaledCellWeight_nonnegative L ell cell) _)).trans
  rw [Finset.mul_sum]
  unfold phaseProductIndexConstant
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro split _
  have coefficientBound := phaseOperatorDerivative_bound admissible dimension cell coordinate
    (derivativeMultiIndex (lowerDerivativeIndex index split))
  change _ ≤ phaseDirectionalConstant L gamma (derivativeOrder (lowerDerivativeIndex index split)) *
    scaledCellWeight L ell cell ^ (derivativeOrder (lowerDerivativeIndex index split) + 1) at coefficientBound
  have orders := derivative_split_order index split
  have indexBound : derivativeOrder index ≤ grade := index.property
  have upperBound : derivativeOrder (upperDerivativeIndex index split) ≤ grade + 1 := by omega
  have inputBound := apWeighted_word_bound L sigma gamma ell cell field upperBound
    (cartesianMultiIndexWord (derivativeMultiIndex (upperDerivativeIndex index split)))
  have powers : grade - derivativeOrder index + (derivativeOrder (lowerDerivativeIndex index split) + 1) =
      grade + 1 - derivativeOrder (upperDerivativeIndex index split) := by omega
  calc
    _ ≤ scaledCellWeight L ell cell ^ (grade - derivativeOrder index) *
        ((splitMultiplicity index split : ℝ) *
          (phaseDirectionalConstant L gamma (derivativeOrder (lowerDerivativeIndex index split)) *
            scaledCellWeight L ell cell ^ (derivativeOrder (lowerDerivativeIndex index split) + 1)) *
          ‖closedDerivativeL2 (derivativeMultiIndex (upperDerivativeIndex index split))
            (apWeightedJet sigma gamma ell cell field)‖) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (scaledCellWeight_nonnegative L ell cell) _)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left coefficientBound (Nat.cast_nonneg _)) (norm_nonneg _)
    _ = ((splitMultiplicity index split : ℝ) * phaseDirectionalConstant L gamma
        (derivativeOrder (lowerDerivativeIndex index split))) *
        (scaledCellWeight L ell cell ^ (grade + 1 - derivativeOrder (upperDerivativeIndex index split)) *
          ‖closedDerivativeL2 (derivativeMultiIndex (upperDerivativeIndex index split))
            (apWeightedJet sigma gamma ell cell field)‖) := by
      rw [← powers, pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left inputBound
      (mul_nonneg (Nat.cast_nonneg _) (phaseDirectionalConstant_nonnegative admissible _))

end Grad.GaugeCoefficients.Physical.Compensated
