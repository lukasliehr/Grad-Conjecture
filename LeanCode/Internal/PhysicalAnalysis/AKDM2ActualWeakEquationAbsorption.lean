import AKDM1ActualPrincipalAbsorption

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.TensorBootstrap Grad.SobolevBridge

/-- Quantitative first absorption for the actual ordered full-cell weak
equation. Its right side is the existing Bessel/flux remainder of the SAME
field, rather than a freely chosen representation of the inverse. -/
theorem startupOrdered_weak_absorption (rank : ℕ)
    (kernels : TensorIndex → StartupOrderedL2 rank →L[ℂ] StartupOrderedL2 rank)
    (small : ‖startupOrderedSecondSum rank kernels‖ ≤ (1 / 8 : ℝ))
    (original zeroth : StartupOrderedL2 rank) (flux : Fin 2 → StartupOrderedL2 rank)
    (equation : ∀ word : DerivativeIndex rank,
      Laplacian.laplacian (distributionEmbedding (original word)) =
        (∑ index : TensorIndex, distributionDerivative index.1
          (distributionDerivative index.2 (distributionEmbedding (kernels index original word)))) +
        distributionEmbedding (zeroth word) +
        ∑ direction : Fin 2, distributionDerivative direction (distributionEmbedding (flux direction word))) :
    ‖original‖ ≤ (8 / 7 : ℝ) *
      ‖startupOrderedValue rank (WithLp.toLp 2 (fun word =>
        startupDivDivRemainder (original word) (zeroth word) (fun direction => flux direction word)))‖ := by
  have identity := startupOrdered_divDiv_resolvent rank kernels original zeroth flux equation
  have triangle := norm_sub_le (original + startupOrderedSecondSum rank kernels original)
    (startupOrderedSecondSum rank kernels original)
  rw [add_sub_cancel_right, identity] at triangle
  have principal := (startupOrderedSecondSum rank kernels).le_opNorm original
  have bound := mul_le_mul_of_nonneg_right small (norm_nonneg original)
  linarith

/-- The adjustable remainder is absorbed after its estimate is proved at a
fixed output rank; the coefficient ball does not depend on that rank. -/
theorem startupOrdered_weak_absorption_remainder (rank : ℕ)
    (kernels : TensorIndex → StartupOrderedL2 rank →L[ℂ] StartupOrderedL2 rank)
    (small : ‖startupOrderedSecondSum rank kernels‖ ≤ (1 / 8 : ℝ))
    (original zeroth : StartupOrderedL2 rank) (flux : Fin 2 → StartupOrderedL2 rank)
    (equation : ∀ word : DerivativeIndex rank,
      Laplacian.laplacian (distributionEmbedding (original word)) =
        (∑ index : TensorIndex, distributionDerivative index.1
          (distributionDerivative index.2 (distributionEmbedding (kernels index original word)))) +
        distributionEmbedding (zeroth word) +
        ∑ direction : Fin 2, distributionDerivative direction (distributionEmbedding (flux direction word)))
    (payment : ℝ)
    (remainder : ‖startupOrderedValue rank (WithLp.toLp 2 (fun word =>
        startupDivDivRemainder (original word) (zeroth word) (fun direction => flux direction word)))‖ ≤
      (7 / 16 : ℝ) * ‖original‖ + payment) :
    ‖original‖ ≤ (16 / 7 : ℝ) * payment := by
  have first := startupOrdered_weak_absorption rank kernels small original zeroth flux equation
  linarith

end Grad.CartesianStartup
