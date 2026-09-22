import MultiplierInterface
import AW3Formulas

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.Constraints.Multipliers

open Grad.ClosedJets Grad.CartesianState Grad.AnalyticWeights
open Grad.AnalyticWeights.Calculus Grad.AnalyticWeights.Higher

theorem frequency_le_polynomial (cell : ℤ) :
    cellFrequency cell ≤ cellPolynomialWeight cell := by
  change Real.sqrt (1 + (cell : ℝ) ^ 2) ≤ 1 + |(cell : ℝ)|
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [sq_abs (cell : ℝ), abs_nonneg (cell : ℝ)]

theorem shifted_frequency_le (input shift : ℤ) :
    cellFrequency (input + shift) ≤ cellPolynomialWeight shift * cellFrequency input := by
  have additive := (cellGoal (input + shift) input).2
  change cellFrequency (input + shift) ≤ cellFrequency input + |(((input + shift) - input : ℤ) : ℝ)| at additive
  simp only [add_sub_cancel_left] at additive
  have inputLower := cellFrequency_one_le input
  rw [cellPolynomialWeight_formula]
  nlinarith [mul_nonneg (abs_nonneg (shift : ℝ)) (sub_nonneg.mpr inputLower)]

theorem shifted_phase_le (parameters : PhaseParameters) (input shift : ℤ)
    (point : ClosedDisk) :
    phaseDifference parameters.sigma0 parameters.gamma 1 (input + shift) input point.val ≤
      parameters.sigma0 * cellFrequency shift := by
  have rateNonnegative : 0 ≤ rate parameters.sigma0 parameters.gamma ‖point.val‖ := by
    have radiusBound : ‖point.val‖ ≤ 1 := point.property
    have widthBound := parameters_gamma_lt_sigma0 parameters
    unfold rate
    nlinarith [parameters.gamma_pos]
  have subadditive := phase_subadditive parameters.sigma0 parameters.gamma ‖point.val‖
    input shift parameters.gamma_pos.le (norm_nonneg _) rateNonnegative
  have oneRoot : 1 ≤ Real.sqrt (1 + ‖point.val‖ ^ 2 * cellFrequency shift ^ 2) :=
    Real.one_le_sqrt.mpr (by nlinarith [mul_nonneg (sq_nonneg ‖point.val‖) (sq_nonneg (cellFrequency shift))])
  have phaseBound : phase parameters.sigma0 parameters.gamma ‖point.val‖ shift ≤
      parameters.sigma0 * cellFrequency shift := by
    change parameters.sigma0 * cellFrequency shift -
      parameters.gamma * (Real.sqrt (1 + ‖point.val‖ ^ 2 * cellFrequency shift ^ 2) - 1) ≤ _
    exact sub_le_self _ (mul_nonneg parameters.gamma_pos.le (sub_nonneg.mpr oneRoot))
  simp only [phaseDifference, physicalPhase, one_mul]
  linarith

theorem shifted_ratio_le (parameters : PhaseParameters) (input shift : ℤ)
    (point : ClosedDisk) :
    weightRatio parameters.sigma0 parameters.gamma 1 (input + shift) input point.val ≤
      Real.exp (parameters.sigma0 * cellFrequency shift) := by
  rw [weightRatio_exp]
  exact Real.exp_le_exp.mpr (shifted_phase_le parameters input shift point)

theorem shifted_allocation_le (rank : ℕ) (input shift : ℤ) :
    allocationPolynomial rank (input + shift) input ≤
      (rank : ℝ) * cellPolynomialWeight shift ^ rank * cellFrequency input ^ rank := by
  unfold allocationPolynomial
  simp only [add_sub_cancel_left]
  have bound : ∀ index ∈ Finset.Icc 1 rank,
      Grad.CellWeights.cellWeight shift ^ index * Grad.CellWeights.cellWeight input ^ (rank - index) ≤
        cellPolynomialWeight shift ^ rank * cellFrequency input ^ rank := by
    intro index membership
    have indexBound := (Finset.mem_Icc.mp membership).2
    apply mul_le_mul
    · exact (pow_le_pow_left₀ (cellFrequency_pos shift).le (frequency_le_polynomial shift) index).trans
        (pow_le_pow_right₀ (cellPolynomialWeight_one_le shift) indexBound)
    · exact pow_le_pow_right₀ (cellFrequency_one_le input) (Nat.sub_le rank index)
    · exact pow_nonneg (cellFrequency_pos input).le _
    · exact pow_nonneg (zero_lt_one.trans_le (cellPolynomialWeight_one_le shift)).le _
  calc
    _ ≤ ∑ _index ∈ Finset.Icc 1 rank,
        cellPolynomialWeight shift ^ rank * cellFrequency input ^ rank := Finset.sum_le_sum bound
    _ = _ := by simp [Nat.card_Icc]; ring

def ratioDerivativeConstant (rank : ℕ) (gamma : ℝ) : ℝ :=
  if rank = 0 then 1 else ratioNormConstant rank * weightCost rank gamma 1 * rank

theorem ratioDerivativeConstant_nonnegative (rank : ℕ) (gamma : ℝ) (gammaNonnegative : 0 ≤ gamma) :
    0 ≤ ratioDerivativeConstant rank gamma := by
  unfold ratioDerivativeConstant
  split_ifs with rankZero
  · norm_num
  · apply mul_nonneg
    · apply mul_nonneg (ratioNormConstant_nonnegative _)
      simp only [weightCost, if_neg rankZero, one_pow, mul_one]
      exact mul_nonneg gammaNonnegative (pow_nonneg (by linarith) _)
    · positivity

theorem shifted_ratio_derivative_le (parameters : PhaseParameters) (input shift : ℤ)
    (rank : ℕ) (point : ClosedDisk) :
    ‖iteratedFDeriv ℝ rank (weightRatio parameters.sigma0 parameters.gamma 1 (input + shift) input)
        point.val‖ ≤
      ratioDerivativeConstant rank parameters.gamma *
        Real.exp (parameters.sigma0 * cellFrequency shift) *
        cellPolynomialWeight shift ^ rank * cellFrequency input ^ rank := by
  by_cases rankZero : rank = 0
  · subst rank
    rw [norm_iteratedFDeriv_zero]
    rw [weightRatio_exp, Real.norm_of_nonneg (Real.exp_pos _).le]
    change Real.exp (phaseDifference parameters.sigma0 parameters.gamma 1 (input + shift) input point.val) ≤
      1 * Real.exp (parameters.sigma0 * cellFrequency shift) * 1 * 1
    simpa only [one_mul, mul_one] using
      Real.exp_le_exp.mpr (shifted_phase_le parameters input shift point)
  · have constantNonnegative : 0 ≤ ratioNormConstant rank * weightCost rank parameters.gamma 1 := by
      apply mul_nonneg (ratioNormConstant_nonnegative _)
      simp only [weightCost, if_neg rankZero, one_pow, mul_one]
      exact mul_nonneg parameters.gamma_pos.le (pow_nonneg (by linarith [parameters.gamma_pos]) _)
    calc
      _ ≤ ratioNormConstant rank * weightCost rank parameters.gamma 1 *
          weightRatio parameters.sigma0 parameters.gamma 1 (input + shift) input point.val *
          allocationPolynomial rank (input + shift) input :=
        weightRatio_iterated_norm_bound _ _ _ _ _ parameters.gamma_pos.le (by positivity)
          rank (by omega) point.val
      _ ≤ ratioNormConstant rank * weightCost rank parameters.gamma 1 *
          Real.exp (parameters.sigma0 * cellFrequency shift) *
          ((rank : ℝ) * cellPolynomialWeight shift ^ rank * cellFrequency input ^ rank) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (shifted_ratio_le parameters input shift point) constantNonnegative
        · exact shifted_allocation_le rank input shift
        · exact Finset.sum_nonneg (fun index _ => mul_nonneg
            (pow_nonneg (Grad.CellWeights.cellWeight_pos _).le _)
            (pow_nonneg (Grad.CellWeights.cellWeight_pos _).le _))
        · exact mul_nonneg constantNonnegative (Real.exp_pos _).le
      _ = _ := by simp only [ratioDerivativeConstant, if_neg rankZero]; ring

end Grad.Constraints.Multipliers
