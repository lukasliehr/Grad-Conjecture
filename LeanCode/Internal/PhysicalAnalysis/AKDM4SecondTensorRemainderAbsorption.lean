import AKDM2ActualWeakEquationAbsorption

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.TensorBootstrap Grad.SobolevBridge

def startupOrderedSecondRemainder (rank : ℕ)
    (tensor : TensorIndex → StartupOrderedL2 rank) : StartupOrderedL2 rank :=
  ∑ index : TensorIndex, hilbertLift (startupSecondL2 index) (tensor index)

theorem startupOrderedSecondRemainder_component (rank : ℕ)
    (tensor : TensorIndex → StartupOrderedL2 rank) (word : DerivativeIndex rank) :
    startupOrderedSecondRemainder rank tensor word =
      ∑ index : TensorIndex, startupSecondL2 index (tensor index word) := by
  change (∑ index : TensorIndex, hilbertLift (startupSecondL2 index) (tensor index)).ofLp word = _
  rw [WithLp.ofLp_sum]
  simp only [Finset.sum_apply,hilbertLift_apply]

theorem startupOrderedSecondRemainder_norm (rank : ℕ)
    (tensor : TensorIndex → StartupOrderedL2 rank) :
    ‖startupOrderedSecondRemainder rank tensor‖ ≤ ∑ index : TensorIndex, ‖tensor index‖ := by
  apply (norm_sum_le Finset.univ _).trans
  apply Finset.sum_le_sum
  intro index _
  exact hilbertLift_norm_le (startupSecondL2 index) (startupSecondL2_opNorm index) (tensor index)

/-- Retain the true L2 tensor remainder under the second resolvent. No
extra derivative or H1 estimate is spent on this lower allocation. -/
theorem startupOrdered_fullRemainder_resolvent (rank : ℕ)
    (kernels : TensorIndex → StartupOrderedL2 rank →L[ℂ] StartupOrderedL2 rank)
    (original zeroth : StartupOrderedL2 rank) (flux : Fin 2 → StartupOrderedL2 rank)
    (tensor : TensorIndex → StartupOrderedL2 rank)
    (equation : ∀ word : DerivativeIndex rank,
      Laplacian.laplacian (distributionEmbedding (original word)) =
        (∑ index : TensorIndex, distributionDerivative index.1
          (distributionDerivative index.2 (distributionEmbedding
            (kernels index original word + tensor index word)))) +
        distributionEmbedding (zeroth word) +
        ∑ direction : Fin 2, distributionDerivative direction (distributionEmbedding (flux direction word))) :
    original + startupOrderedSecondSum rank kernels original =
      startupOrderedValue rank (WithLp.toLp 2 (fun word =>
        startupDivDivRemainder (original word) (zeroth word) (fun direction => flux direction word))) -
      startupOrderedSecondRemainder rank tensor := by
  apply PiLp.ext
  intro word
  change original word + startupOrderedSecondSum rank kernels original word =
    valueInclusion (startupDivDivRemainder (original word) (zeroth word) (fun direction => flux direction word)) -
      startupOrderedSecondRemainder rank tensor word
  rw [startupOrderedSecondSum_component,startupOrderedSecondRemainder_component]
  apply distributionEmbedding_injective
  rw [map_add,map_sub,map_sum,startupDivDivRemainder_distribution,map_sum]
  simp only [startupSecondL2_distribution,← map_sum]
  have recovered := distributionResolvent_left (distributionEmbedding (original word))
  rw [equation word] at recovered
  simp only [map_add,Finset.sum_add_distrib] at recovered
  have rearranged : distributionEmbedding (original word) -
      (((∑ index : TensorIndex, distributionDerivative index.1
        (distributionDerivative index.2 (distributionEmbedding (kernels index original word)))) +
        ∑ index : TensorIndex, distributionDerivative index.1
          (distributionDerivative index.2 (distributionEmbedding (tensor index word)))) +
        distributionEmbedding (zeroth word) +
        ∑ direction : Fin 2, distributionDerivative direction (distributionEmbedding (flux direction word))) =
      ((distributionEmbedding (original word) - distributionEmbedding (zeroth word) -
        ∑ direction : Fin 2, distributionDerivative direction (distributionEmbedding (flux direction word))) -
        ∑ index : TensorIndex, distributionDerivative index.1
          (distributionDerivative index.2 (distributionEmbedding (tensor index word)))) -
        ∑ index : TensorIndex, distributionDerivative index.1
          (distributionDerivative index.2 (distributionEmbedding (kernels index original word))) := by abel
  rw [rearranged,map_sub,map_sub] at recovered
  exact (sub_eq_iff_eq_add.mp recovered).symm

/-- First CT absorption with the complete actual second-tensor remainder. -/
theorem startupOrdered_fullRemainder_absorption (rank : ℕ)
    (kernels : TensorIndex → StartupOrderedL2 rank →L[ℂ] StartupOrderedL2 rank)
    (small : ‖startupOrderedSecondSum rank kernels‖ ≤ (1 / 8 : ℝ))
    (original zeroth : StartupOrderedL2 rank) (flux : Fin 2 → StartupOrderedL2 rank)
    (tensor : TensorIndex → StartupOrderedL2 rank)
    (equation : ∀ word : DerivativeIndex rank,
      Laplacian.laplacian (distributionEmbedding (original word)) =
        (∑ index : TensorIndex, distributionDerivative index.1
          (distributionDerivative index.2 (distributionEmbedding
            (kernels index original word + tensor index word)))) +
        distributionEmbedding (zeroth word) +
        ∑ direction : Fin 2, distributionDerivative direction (distributionEmbedding (flux direction word))) :
    ‖original‖ ≤ (8 / 7 : ℝ) *
      (‖startupOrderedValue rank (WithLp.toLp 2 (fun word =>
        startupDivDivRemainder (original word) (zeroth word) (fun direction => flux direction word)))‖ +
        ∑ index : TensorIndex, ‖tensor index‖) := by
  have identity := startupOrdered_fullRemainder_resolvent rank kernels original zeroth flux tensor equation
  have triangle := norm_sub_le (original + startupOrderedSecondSum rank kernels original)
    (startupOrderedSecondSum rank kernels original)
  rw [add_sub_cancel_right,identity] at triangle
  have second := norm_sub_le
    (startupOrderedValue rank (WithLp.toLp 2 (fun word =>
      startupDivDivRemainder (original word) (zeroth word) (fun direction => flux direction word))))
    (startupOrderedSecondRemainder rank tensor)
  have tensorBound := startupOrderedSecondRemainder_norm rank tensor
  have principal := (startupOrderedSecondSum rank kernels).le_opNorm original
  have bound := mul_le_mul_of_nonneg_right small (norm_nonneg original)
  linarith

end Grad.CartesianStartup
