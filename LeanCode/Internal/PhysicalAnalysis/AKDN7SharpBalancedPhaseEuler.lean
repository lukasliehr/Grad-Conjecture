import AKDH17ActualPhysicalOperatorEuler
import AKCI5OriginalBalancedPhaseOrder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.PhaseAlgebra Grad.AnnularWeightedSmoothness Grad.AnnularVariational
open Grad.SourceCollarCoefficients Grad.SourceBoundaryTrace

/-- Literal balanced diagonal scalar D(Phi)-1. -/
def actualBalancedPhaseScalar (parameters : PhaseParameters) (cell : ℤ) (radius : ℝ) : ℝ :=
  radius * annularPhaseSlope parameters cell radius-1

theorem actualBalancedPhaseScalar_smooth (parameters : PhaseParameters) (cell : ℤ) :
    ContDiff ℝ ∞ (actualBalancedPhaseScalar parameters cell) :=
  (contDiff_id.mul (annularPhaseSlope_smooth parameters cell)).sub contDiff_const

theorem eulerIteratedDerivative_right (field : ℝ → ℝ) (rank : ℕ) :
    eulerIteratedDerivative rank (eulerDerivative field) = eulerIteratedDerivative (rank+1) field := by
  induction rank with
  | zero => rfl
  | succ rank previous => exact congrArg eulerDerivative previous

theorem eulerIteratedDerivative_const (value : ℝ) (rank : ℕ) :
    eulerIteratedDerivative rank (fun _ => value) = fun _ => if rank=0 then value else 0 := by
  induction rank with
  | zero => rfl
  | succ rank previous =>
      change eulerDerivative (eulerIteratedDerivative rank (fun _ => value)) = _
      rw [previous]
      funext radius
      simp only [eulerDerivative,deriv_const,mul_zero,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false]

theorem actualBalancedPhaseScalar_euler (parameters : PhaseParameters) (cell : ℤ) (rank : ℕ) :
    eulerIteratedDerivative rank (actualBalancedPhaseScalar parameters cell) =
      fun radius => eulerIteratedDerivative (rank+1) (fun point => radialPhase parameters point cell) radius-
        if rank=0 then 1 else 0 := by
  have literal : actualBalancedPhaseScalar parameters cell =
      fun radius => eulerDerivative (fun point => radialPhase parameters point cell) radius-1 := by
    funext radius
    rw [actualBalancedPhaseScalar,annularPhaseSlope_eq_deriv]
    rfl
  have phaseSmooth : ContDiff ℝ ∞ (eulerDerivative (fun point => radialPhase parameters point cell)) :=
    eulerIteratedDerivative_smooth _ (radialPhase_smooth parameters cell) 1
  rw [literal,eulerIteratedDerivative_sub _ _ phaseSmooth contDiff_const,
    eulerIteratedDerivative_right,eulerIteratedDerivative_const]

def balancedPhaseEulerConstant (parameters : PhaseParameters) (rank : ℕ) : ℝ :=
  positiveEulerPhaseConstant parameters rank+1

theorem balancedPhaseEulerConstant_nonnegative (parameters : PhaseParameters) (rank : ℕ) :
    0 ≤ balancedPhaseEulerConstant parameters rank :=
  add_nonneg (positiveEulerPhaseConstant_nonnegative parameters rank) zero_le_one

/-- Every positive radial differentiation still consumes only one original
frequency. The constant depends on rank, never on a cell or coefficient state. -/
theorem actualBalancedPhaseScalar_euler_bound (parameters : PhaseParameters) (rank : ℕ)
    (mode : ℤ × ℤ) (radius : ℝ) (inside : radius ∈ Icc 0 1) :
    ‖eulerIteratedDerivative rank (actualBalancedPhaseScalar parameters mode.2) radius‖ ≤
      balancedPhaseEulerConstant parameters rank * annularFrequency mode.1 mode.2 := by
  have frequencyOne : 1 ≤ annularFrequency mode.1 mode.2 := by
    unfold annularFrequency
    linarith [abs_nonneg (mode.1 : ℝ),abs_nonneg (mode.2 : ℝ)]
  have cell : cellFrequency mode.2 ≤ annularFrequency mode.1 mode.2 := by
    apply (cellFrequency_le_polynomial mode.2).trans
    change 1+|(mode.2 : ℝ)| ≤ 1+|(mode.1 : ℝ)|+|(mode.2 : ℝ)|
    linarith [abs_nonneg (mode.1 : ℝ)]
  have constant : ‖(if rank=0 then (1 : ℝ) else 0)‖ ≤ 1 := by split_ifs <;> norm_num
  rw [actualBalancedPhaseScalar_euler]
  exact (norm_sub_le _ _).trans ((add_le_add
    ((radialPhase_positiveEuler_bound parameters rank mode.2 radius inside).trans
      (mul_le_mul_of_nonneg_left cell (positiveEulerPhaseConstant_nonnegative parameters rank))) constant).trans
        (by dsimp only [balancedPhaseEulerConstant]; nlinarith))

section ScalarFidelity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Genuine closed-interval Euler derivatives of a fixed vector times a
smooth real scalar. Used after bounded coefficient observation. -/
theorem vectorEulerWithin_fixedScalar (domain : Set ℝ) (unique : UniqueDiffOn ℝ domain)
    (nonzero : ∀ point ∈ domain, point ≠ 0) (scalar : ℝ → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (value : E) (rank : ℕ) (radius : ℝ) (inside : radius ∈ domain) :
    vectorEulerWithinIteratedDerivative domain rank (fun point => scalar point • value) radius =
      eulerIteratedDerivative rank scalar radius • value := by
  apply vectorEulerWithinIteratedDerivative_tower domain unique nonzero
    (fun order point => eulerIteratedDerivative order scalar point • value) _ rank inside
  intro order point member
  have derivative := (actualScalarEulerJets_hasDerivWithinAt domain scalar smooth order point (nonzero point member)).smul_const value
  simpa only [smul_smul,smul_eq_mul] using derivative

end ScalarFidelity
end Grad.OriginalCartesianTameEstimate
