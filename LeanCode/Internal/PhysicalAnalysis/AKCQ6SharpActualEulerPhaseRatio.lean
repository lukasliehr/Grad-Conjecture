import AKCQ5ScalarExponentialJetAllocation
import AKC12ActualPhaseRatioJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.PhaseAlgebra Grad.AnnularWeightedSmoothness Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.BoundaryKernelAction

/-- The same phase difference along exp(time), used only to identify actual
Euler derivatives with ordinary derivatives in the finite chain rule. -/
def phaseLogDifference (parameters : PhaseParameters) (output input : ℤ) (time : ℝ) : ℝ :=
  radialPhase parameters (Real.exp time) output-radialPhase parameters (Real.exp time) input

theorem phaseLogDifference_smooth (parameters : PhaseParameters) (output input : ℤ) :
    ContDiff ℝ ∞ (phaseLogDifference parameters output input) :=
  ((radialPhase_smooth parameters output).comp Real.contDiff_exp).sub
    ((radialPhase_smooth parameters input).comp Real.contDiff_exp)

theorem phaseLogDifference_iterated_bound (parameters : PhaseParameters) (output input : ℤ)
    (time : ℝ) (upper : Real.exp time ≤ 1) (weight : ℝ) (one : 1 ≤ weight)
    (displacement : |((output-input : ℤ) : ℝ)| ≤ weight) (order : ℕ) (positive : 1 ≤ order) :
    ‖iteratedDeriv order (phaseLogDifference parameters output input) time‖ ≤
      positiveEulerPhaseConstant parameters (order-1) * weight^order := by
  have same := iteratedDeriv_comp_exp_euler
    (fun radius => radialPhase parameters radius output-radialPhase parameters radius input)
    ((radialPhase_smooth parameters output).sub (radialPhase_smooth parameters input)) order
  change ‖iteratedDeriv order (fun location =>
    radialPhase parameters (Real.exp location) output-radialPhase parameters (Real.exp location) input) time‖ ≤ _
  rw [same,eulerIteratedDerivative_sub _ _ (radialPhase_smooth parameters output) (radialPhase_smooth parameters input)]
  have phase := radialPhase_positiveEuler_difference parameters (order-1) output input (Real.exp time) (Real.exp_pos _).le
  rw [Nat.sub_add_cancel positive] at phase
  have constant0 := positiveEulerPhaseConstant_nonnegative parameters (order-1)
  have degree : weight ≤ weight^order := by
    simpa only [pow_one] using pow_le_pow_right₀ one positive
  calc
    _ ≤ positiveEulerPhaseConstant parameters (order-1) * Real.exp time * |((output-input : ℤ) : ℝ)| := phase
    _ ≤ positiveEulerPhaseConstant parameters (order-1) * weight := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        ((mul_le_mul upper displacement (abs_nonneg _) zero_le_one).trans_eq (one_mul _)) constant0
    _ ≤ _ := mul_le_mul_of_nonneg_left degree constant0

def positiveEulerRatioConstant (parameters : PhaseParameters) (rank : ℕ) : ℝ :=
  1 + scalarExpJetConstant (fun order => positiveEulerPhaseConstant parameters (order-1)) rank

theorem positiveEulerRatioConstant_one_le (parameters : PhaseParameters) (rank : ℕ) :
    1 ≤ positiveEulerRatioConstant parameters rank :=
  le_add_of_nonneg_right (scalarExpJetConstant_nonnegative _
    (fun order => positiveEulerPhaseConstant_nonnegative parameters (order-1)) rank)

/-- The original exponential ratio has a full actual Euler derivative bound
with one total displacement rank and no input-cell power. -/
theorem radialPhaseRatio_euler_weightBound (parameters : PhaseParameters) (rank : ℕ)
    (output input : ℤ) (radius : ℝ) (inside : radius ∈ Icc 0 1)
    (weight : ℝ) (one : 1 ≤ weight) (displacement : |((output-input : ℤ) : ℝ)| ≤ weight) :
    ‖eulerIteratedDerivative rank (radialPhaseRatio parameters output input) radius‖ ≤
      positiveEulerRatioConstant parameters rank * radialPhaseRatio parameters output input radius * weight^rank := by
  have weight0 := zero_le_one.trans one
  have constant0 := zero_le_one.trans (positiveEulerRatioConstant_one_le parameters rank)
  have ratio0 : 0 ≤ radialPhaseRatio parameters output input radius := (Real.exp_pos _).le
  by_cases zero : radius = 0
  · subst radius
    cases rank with
    | zero =>
        change ‖radialPhaseRatio parameters output input 0‖ ≤ _
        rw [Real.norm_of_nonneg ratio0,pow_zero,mul_one]
        exact le_mul_of_one_le_left ratio0 (positiveEulerRatioConstant_one_le parameters 0)
    | succ rank =>
        rw [eulerIteratedDerivative_zero,norm_zero]
        exact mul_nonneg (mul_nonneg constant0 ratio0) (pow_nonneg weight0 _)
  have positive : 0 < radius := lt_of_le_of_ne inside.1 (Ne.symm zero)
  let constants := fun order => positiveEulerPhaseConstant parameters (order-1)
  have paid := scalarExp_iterated_bound (phaseLogDifference parameters output input)
    (phaseLogDifference_smooth parameters output input) constants
    weight (Real.log radius)
    (fun order orderPositive => phaseLogDifference_iterated_bound parameters output input (Real.log radius)
      (by simpa only [Real.exp_log positive] using inside.2) weight one displacement order orderPositive) rank
  have actual : iteratedDeriv rank (fun time => Real.exp (phaseLogDifference parameters output input time)) (Real.log radius) =
      eulerIteratedDerivative rank (radialPhaseRatio parameters output input) radius := by
    have same := congrFun (iteratedDeriv_comp_exp_euler (radialPhaseRatio parameters output input)
      (radialPhaseRatio_smooth parameters output input) rank) (Real.log radius)
    simpa only [radialPhaseRatio,phaseLogDifference,Real.exp_log positive] using same
  have phaseValue : Real.exp (phaseLogDifference parameters output input (Real.log radius)) =
      radialPhaseRatio parameters output input radius := by
    simp only [phaseLogDifference,Real.exp_log positive,radialPhaseRatio]
  rw [actual,phaseValue] at paid
  apply paid.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) ratio0) (pow_nonneg weight0 _)

/-- Exact two-angle kernel consumer: only the displacement mode appears;
all input cells are retained at their original phase. -/
theorem radialPhaseRatio_euler_displacement (parameters : PhaseParameters) (rank : ℕ)
    (shift input : ℤ × ℤ) (radius : RadialPoint) :
    ‖eulerIteratedDerivative rank
      (radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2) radius.val‖ ≤
      positiveEulerRatioConstant parameters rank *
        radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2 radius.val *
          annularFrequency shift.1 shift.2 ^ rank := by
  apply radialPhaseRatio_euler_weightBound parameters rank _ _ radius.val radius.property _
    (Grad.AnnularWeightedSmoothness.annularFrequency_one_le shift)
  have difference : ((twoFrequencyTranslation shift).symm input).2-input.2 = shift.2 := by
    simp [twoFrequencyTranslation]
  rw [difference]
  change |(shift.2 : ℝ)| ≤ 1+|(shift.1 : ℝ)|+|(shift.2 : ℝ)|
  linarith [abs_nonneg (shift.1 : ℝ)]

end Grad.OriginalCartesianTameEstimate
