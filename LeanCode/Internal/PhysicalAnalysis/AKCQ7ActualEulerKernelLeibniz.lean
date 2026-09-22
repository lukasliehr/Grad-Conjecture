import AKCQ6SharpActualEulerPhaseRatio
import AKC13ActualMatrixJetCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set
open scoped ContDiff BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.PhaseAlgebra Grad.AnnularWeightedSmoothness
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularVariational

section Vector
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual Euler derivatives of a vector or matrix entry. -/
def vectorEulerDerivative (field : ℝ → E) (radius : ℝ) : E := radius • deriv field radius

def vectorEulerIteratedDerivative (rank : ℕ) (field : ℝ → E) : ℝ → E :=
  Nat.rec field (fun _ previous => vectorEulerDerivative previous) rank

theorem vectorEulerIteratedDerivative_smooth (field : ℝ → E)
    (smooth : ContDiff ℝ ∞ field) (rank : ℕ) :
    ContDiff ℝ ∞ (vectorEulerIteratedDerivative rank field) := by
  induction rank with
  | zero => exact smooth
  | succ rank previous => exact contDiff_id.smul (contDiff_infty_iff_deriv.mp previous).2

theorem iteratedDeriv_comp_exp_vectorEuler (field : ℝ → E)
    (smooth : ContDiff ℝ ∞ field) (rank : ℕ) :
    iteratedDeriv rank (fun time => field (Real.exp time)) =
      fun time => vectorEulerIteratedDerivative rank field (Real.exp time) := by
  induction rank with
  | zero => rfl
  | succ rank previous =>
      rw [iteratedDeriv_succ,previous]
      funext time
      have derivative := (((vectorEulerIteratedDerivative_smooth field smooth rank).differentiable
        (by simp) (Real.exp time)).hasDerivAt).scomp time (Real.hasDerivAt_exp time)
      simp only [Function.comp_def] at derivative
      exact derivative.deriv

/-- Genuine Leibniz allocation: the two Euler ranks sum to the requested
rank before any coefficient estimate is applied. -/
theorem vectorEulerIteratedDerivative_real_smul (scalar : ℝ → ℝ) (vector : ℝ → E)
    (one : ContDiff ℝ ∞ scalar) (two : ContDiff ℝ ∞ vector)
    (rank : ℕ) (radius : ℝ) (positive : 0 < radius) :
    vectorEulerIteratedDerivative rank (fun point => scalar point • vector point) radius =
      ∑ index ∈ Finset.range (rank+1),
        rank.choose index • eulerIteratedDerivative index scalar radius •
          vectorEulerIteratedDerivative (rank-index) vector radius := by
  have product := iteratedDeriv_real_smul rank (Real.log radius)
    (one.comp Real.contDiff_exp) (two.comp Real.contDiff_exp)
  simp only [Function.comp_def] at product
  rw [iteratedDeriv_comp_exp_vectorEuler (fun point => scalar point • vector point) (one.smul two)] at product
  simp only [iteratedDeriv_comp_exp_euler _ one,
    iteratedDeriv_comp_exp_vectorEuler _ two,Real.exp_log positive] at product
  exact product

/-- SR12 at the literal scalar-conjugated matrix entry. The commutator
coefficient is the output-input difference of the actual phase derivatives. -/
theorem vectorEuler_phaseConjugate (parameters : PhaseParameters) (output input : ℤ)
    (coefficient : ℝ → E) (smooth : ContDiff ℝ ∞ coefficient) (radius : ℝ) :
    vectorEulerDerivative (fun point => radialPhaseRatio parameters output input point • coefficient point) radius =
      radialPhaseRatio parameters output input radius • vectorEulerDerivative coefficient radius +
        (eulerDerivative (fun point => radialPhase parameters point output) radius-
          eulerDerivative (fun point => radialPhase parameters point input) radius) •
          (radialPhaseRatio parameters output input radius • coefficient radius) := by
  have phase := ((radialPhase_smooth parameters output).differentiable (by simp) radius).hasDerivAt.sub
    (((radialPhase_smooth parameters input).differentiable (by simp) radius).hasDerivAt)
  have ratio := phase.exp
  simp only [Pi.sub_def] at ratio
  have product := ratio.smul ((smooth.differentiable (by simp) radius).hasDerivAt)
  simp only [radialPhaseRatio] at product ⊢
  change HasDerivAt (fun point => Real.exp (radialPhase parameters point output-
    radialPhase parameters point input) • coefficient point) _ radius at product
  change radius • deriv (fun point => Real.exp (radialPhase parameters point output-
    radialPhase parameters point input) • coefficient point) radius = _
  rw [product.deriv]
  simp only [vectorEulerDerivative,eulerDerivative,smul_add,smul_smul]
  module

/-- Full original phase, all input cells and the exact finite rank
allocation. The scalar part pays displacement moments only. -/
theorem vectorEuler_phaseConjugate_norm (parameters : PhaseParameters) (rank : ℕ)
    (shift input : ℤ × ℤ) (radius : RadialPoint) (positive : 0 < radius.val)
    (coefficient : ℝ → E) (smooth : ContDiff ℝ ∞ coefficient) :
    ‖vectorEulerIteratedDerivative rank (fun point =>
      radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2 point •
        coefficient point) radius.val‖ ≤
      ∑ index ∈ Finset.range (rank+1),
        (rank.choose index : ℝ) * positiveEulerRatioConstant parameters index *
          radialPhaseRatio parameters ((twoFrequencyTranslation shift).symm input).2 input.2 radius.val *
            annularFrequency shift.1 shift.2 ^ index *
              ‖vectorEulerIteratedDerivative (rank-index) coefficient radius.val‖ := by
  rw [vectorEulerIteratedDerivative_real_smul _ _ (radialPhaseRatio_smooth parameters _ _) smooth rank radius.val positive]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro index _
  rw [← Nat.cast_smul_eq_nsmul ℝ,norm_smul,Real.norm_natCast,norm_smul]
  have ratio := radialPhaseRatio_euler_displacement parameters index shift input radius
  have paid := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right ratio (norm_nonneg (vectorEulerIteratedDerivative (rank-index) coefficient radius.val))) (Nat.cast_nonneg (rank.choose index))
  convert paid using 1; ring

end Vector
end Grad.OriginalCartesianTameEstimate
