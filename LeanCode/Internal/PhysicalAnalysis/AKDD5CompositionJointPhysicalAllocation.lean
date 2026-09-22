import AKDD4ActualCompositionEulerKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.GaugeCoefficients.Physical.Allocation

theorem compositionEulerKernel_moment_le {parameters : PhaseParameters} {source middle target : ℕ}
    (radius : RadialPoint) (outer : ℕ → RadialKernel parameters radius middle target)
    (inner : ℕ → RadialKernel parameters radius source middle) (terms : List (ℕ × ℕ)) (moment : ℕ) :
    fullKernelMoment (radialKernelParameters parameters radius) moment (compositionEulerKernel radius outer inner terms) ≤
      eulerAllocationSum (fun first second => fullKernelMoment (radialKernelParameters parameters radius) moment
        (fullKernelComposition (outer first) (inner second))) terms := by
  induction terms with
  | nil => exact (fullKernelSmul_moment_le 0 _ moment).trans_eq (by simp [eulerAllocationSum])
  | cons term terms previous => exact (fullKernelAdd_moment_le _ moment _ _).trans (add_le_add le_rfl previous)

def compositionEulerMomentConstant (offset : ℕ) (outer inner : ℕ → ℕ → ℝ) (rank moment : ℕ) : ℝ :=
  eulerAllocationSum (fun first second => 2^moment *
    (outer first moment*inner second 0+outer first 0*inner second moment) *
      (3+pairBudgetConstant offset (rank+moment) 1)) (eulerLeibnizTerms rank)

theorem compositionEulerMomentConstant_nonnegative (offset : ℕ) (outer inner : ℕ → ℕ → ℝ)
    (outer0 : ∀ rank moment, 0 ≤ outer rank moment) (inner0 : ∀ rank moment, 0 ≤ inner rank moment)
    (rank moment : ℕ) : 0 ≤ compositionEulerMomentConstant offset outer inner rank moment := by
  apply eulerAllocationSum_nonnegative
  intro first second
  have pair0 := pairBudgetConstant_nonnegative offset (rank+moment) (lowBound := (1 : ℝ)) zero_le_one
  exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) moment)
    (add_nonneg (mul_nonneg (outer0 first moment) (inner0 second 0))
      (mul_nonneg (outer0 first 0) (inner0 second moment)))) (by linarith)

/-- Rectangular composition spends the total derivative and displacement
rank once. The full convolution and both high/low alternatives remain
inside the joint interpolation estimate, so no high×high loss occurs. -/
theorem compositionEulerKernel_oneHigh {source middle target : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters 3) (rho epsilon : ℝ) (radius : RadialPoint) (offset : ℕ)
    (low : physicalBudget parameters field rho epsilon offset ≤ 1)
    (outer : ℕ → RadialKernel parameters radius middle target)
    (inner : ℕ → RadialKernel parameters radius source middle)
    (outerConstants innerConstants : ℕ → ℕ → ℝ)
    (outer0 : ∀ rank moment, 0 ≤ outerConstants rank moment)
    (inner0 : ∀ rank moment, 0 ≤ innerConstants rank moment)
    (outerBound : ∀ rank moment, fullKernelMoment (radialKernelParameters parameters radius) moment (outer rank) ≤
      outerConstants rank moment*(1+physicalBudget parameters field rho epsilon (offset+(rank+moment))))
    (innerBound : ∀ rank moment, fullKernelMoment (radialKernelParameters parameters radius) moment (inner rank) ≤
      innerConstants rank moment*(1+physicalBudget parameters field rho epsilon (offset+(rank+moment))))
    (rank moment : ℕ) :
    fullKernelMoment (radialKernelParameters parameters radius) moment
      (compositionEulerKernel radius outer inner (eulerLeibnizTerms rank)) ≤
      compositionEulerMomentConstant offset outerConstants innerConstants rank moment *
        (1+physicalBudget parameters field rho epsilon (offset+(rank+moment))) := by
  apply (compositionEulerKernel_moment_le radius outer inner _ moment).trans
  let size := 1+physicalBudget parameters field rho epsilon (offset+(rank+moment))
  have paid : eulerAllocationSum (fun first second => fullKernelMoment (radialKernelParameters parameters radius) moment
        (fullKernelComposition (outer first) (inner second))) (eulerLeibnizTerms rank) ≤
      eulerAllocationSum (fun first second => size*(2^moment *
        (outerConstants first moment*innerConstants second 0+outerConstants first 0*innerConstants second moment)*
          (3+pairBudgetConstant offset (rank+moment) 1))) (eulerLeibnizTerms rank) := by
    apply eulerAllocationSum_mono
    intro term member
    have degree := eulerLeibnizTerms_rank rank term member
    have result := fullKernelComposition_joint_oneHigh parameters field rho epsilon radius offset (rank+moment)
      term.1 term.2 moment (by omega) low (outer term.1) (inner term.2)
      (outerConstants term.1 moment) (outerConstants term.1 0) (innerConstants term.2 moment) (innerConstants term.2 0)
      (outer0 _ _) (outer0 _ _) (inner0 _ _) (inner0 _ _)
      (outerBound _ _) (by simpa only [Nat.add_zero] using outerBound term.1 0)
      (innerBound _ _) (by simpa only [Nat.add_zero] using innerBound term.2 0)
    exact result.trans_eq (mul_comm _ _)
  apply paid.trans_eq
  rw [← eulerAllocationSum_mul_left]
  exact mul_comm _ _

end Grad.OriginalCartesianTameEstimate
