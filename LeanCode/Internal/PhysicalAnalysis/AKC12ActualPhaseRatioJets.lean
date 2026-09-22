import AKC9ReservedMatrixDecay
import AKH1ActualPhaseSlopeJets
import AW3Exponential
import AW3Formulas

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 350000
open Set
open scoped BigOperators ENNReal Topology ContDiff
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.BoundaryLift Grad.AnnularKernelL2
open Grad.AnnularReconstruction Grad.AnnularKernelContinuity Grad.PhaseAlgebra
open Grad.AnalyticWeights.Calculus Grad.AnalyticWeights.Higher

def radialPhaseRatio (parameters : PhaseParameters) (output input : ℤ) (radius : ℝ) : ℝ :=
  Real.exp (radialPhase parameters radius output - radialPhase parameters radius input)

theorem radialPhaseRatio_ray (parameters : PhaseParameters) (output input : ℤ) :
    radialPhaseRatio parameters output input =
      weightRatio parameters.sigma0 parameters.gamma 1 output input ∘ phaseRadialRay := by
  funext radius
  rw [Function.comp_apply, weightRatio_exp]
  change Real.exp (radialPhase parameters radius output - radialPhase parameters radius input) =
    Real.exp (cartesianPhase parameters output (phaseRadialRay radius) - cartesianPhase parameters input (phaseRadialRay radius))
  rw [congrFun (radialPhase_ray parameters output) radius, congrFun (radialPhase_ray parameters input) radius]
  rfl

theorem radialPhaseRatio_smooth (parameters : PhaseParameters) (output input : ℤ) :
    ContDiff ℝ ∞ (radialPhaseRatio parameters output input) := by
  rw [radialPhaseRatio_ray]
  exact (weightRatio_contDiff parameters.sigma0 parameters.gamma 1 output input).comp phaseRadialRay.contDiff

theorem annularFrequency_one_le (mode : ℤ × ℤ) : 1 ≤ annularFrequency mode.1 mode.2 := by
  change 1 ≤ 1 + |(mode.1 : ℝ)| + |(mode.2 : ℝ)|
  linarith [abs_nonneg (mode.1 : ℝ), abs_nonneg (mode.2 : ℝ)]

theorem allocationPolynomial_annular_bound (rank : ℕ) (shift input : ℤ × ℤ) :
    allocationPolynomial rank ((twoFrequencyTranslation shift).symm input).2 input.2 ≤
      ((Finset.Icc 1 rank).card : ℝ) * annularFrequency shift.1 shift.2 ^ rank *
        annularFrequency input.1 input.2 ^ rank := by
  have cellBound (mode : ℤ × ℤ) : Grad.CellWeights.cellWeight mode.2 ≤ annularFrequency mode.1 mode.2 := by
    apply (cellFrequency_le_polynomial mode.2).trans
    change 1 + |(mode.2 : ℝ)| ≤ 1 + |(mode.1 : ℝ)| + |(mode.2 : ℝ)|
    linarith [abs_nonneg (mode.1 : ℝ)]
  have difference : ((twoFrequencyTranslation shift).symm input).2 - input.2 = shift.2 := by
    simp [twoFrequencyTranslation]
  unfold allocationPolynomial
  rw [difference]
  calc
    _ ≤ ∑ _index ∈ Finset.Icc 1 rank,
        annularFrequency shift.1 shift.2 ^ rank * annularFrequency input.1 input.2 ^ rank := by
      apply Finset.sum_le_sum
      intro index hi
      have first := (pow_le_pow_left₀ (cellFrequency_pos shift.2).le (cellBound shift) index).trans
        (pow_le_pow_right₀ (annularFrequency_one_le shift) (Finset.mem_Icc.mp hi).2)
      have second := (pow_le_pow_left₀ (cellFrequency_pos input.2).le (cellBound input) (rank - index)).trans
        (pow_le_pow_right₀ (annularFrequency_one_le input) (Nat.sub_le rank index))
      exact mul_le_mul first second (pow_nonneg (cellFrequency_pos input.2).le _) (pow_nonneg (annularFrequency_pos shift).le _)
    _ = _ := by simp [mul_assoc]

def phaseRatioJetConstant (parameters : PhaseParameters) (rank : ℕ) : ℝ :=
  if rank = 0 then 1 else ratioNormConstant rank * weightCost rank parameters.gamma 1 * ((Finset.Icc 1 rank).card : ℝ)

theorem phaseRatioJetConstant_nonnegative (parameters : PhaseParameters) (rank : ℕ) :
    0 ≤ phaseRatioJetConstant parameters rank := by
  have nonnegative := ratioNormConstant_nonnegative rank
  have gamma := parameters.gamma_pos
  unfold phaseRatioJetConstant weightCost
  split_ifs <;> positivity

theorem radialPhaseRatio_iterated_bound (parameters : PhaseParameters) (rank : ℕ)
    (shift input : ℤ × ℤ) (radius : ℝ) :
    ‖iteratedDeriv rank (radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2) radius‖ ≤
      phaseRatioJetConstant parameters rank *
        radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2 radius *
          annularFrequency shift.1 shift.2 ^ rank * annularFrequency input.1 input.2 ^ rank := by
  by_cases zero : rank = 0
  · subst rank
    simp [phaseRatioJetConstant, iteratedDeriv_zero, radialPhaseRatio, Real.norm_eq_abs]
  have positiveRank : 1 ≤ rank := by omega
  rw [radialPhaseRatio_ray]
  apply (radialRay_iteratedDeriv_bound _
    (weightRatio_contDiff parameters.sigma0 parameters.gamma 1 _ _) rank radius).trans
  apply (weightRatio_iterated_norm_bound parameters.sigma0 parameters.gamma 1 _ _
    parameters.gamma_pos.le (by norm_num) rank positiveRank (phaseRadialRay radius)).trans
  have scalarNonnegative : 0 ≤ ratioNormConstant rank * weightCost rank parameters.gamma 1 *
      weightRatio parameters.sigma0 parameters.gamma 1 ((twoFrequencyTranslation shift).symm input).2 input.2 (phaseRadialRay radius) := by
    have ratio := (ratioGoal parameters.sigma0 parameters.gamma 1 ((twoFrequencyTranslation shift).symm input).2 input.2
      (phaseRadialRay radius)).1
    have factor := ratioNormConstant_nonnegative rank
    have gamma := parameters.gamma_pos
    unfold weightCost
    split_ifs
    positivity
  apply (mul_le_mul_of_nonneg_left (allocationPolynomial_annular_bound rank shift input) scalarNonnegative).trans_eq
  simp only [phaseRatioJetConstant, zero, ite_false, Function.comp_apply]
  ring

end Grad.AnnularWeightedSmoothness
