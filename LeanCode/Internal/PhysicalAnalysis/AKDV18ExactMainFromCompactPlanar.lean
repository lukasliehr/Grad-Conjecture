import AKDV17ActualCompactPlanarInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
open Set
open scoped ContDiff
namespace Grad.OriginalMainConsumer
open Grad.CartesianState Grad.Constraints Grad.PhysicalFamily Grad.PhysicalGeometry
open Grad.OriginalInverseNeighborhood Grad.PDEBootstrap

/-- Exact unchanged Main from the actual canonical compact planar estimate.
The same original product, native solve, current recovery, both inverse laws,
Newton scale, smooth cell family and full ambient geometry are constructed. -/
theorem exact_main_of_actual_compact_planar
    (analytic : ∀ (length : ℝ) (positive : 0<length),
      let parameters := mainPhaseParameters length positive
      ∃ (outer : Spatial→ℝ) (smooth : ContDiff ℝ ∞ outer) (compact : HasCompactSupport outer)
        (higher shift loss : ℕ) (higherLarge : 24≤higher),
        shift+32≤loss ∧ loss+8≤higher ∧
        Nonempty (ActualProductCompactPlanarEstimate
          (actualPrincipalProduct parameters parameters.length_pos originalSeedCenter originalSeedCenter_inside
            originalSeedCenter originalSeedCenter_inside originalSeedCenter_zero outer smooth compact)
          (mainPhaseParameters_widthHalf length positive) (mainPhaseParameters_widthLength length positive)
          higher higherLarge shift)) : Grad.MainTarget.mainTheoremStatement := by
  apply exact_main_of_original_oneHigh
  intro length positive
  obtain ⟨outer,smooth,compact,higher,shift,loss,higherLarge,lossLarge,lowFits,⟨estimate⟩⟩ := analytic length positive
  exact ⟨_,higher,loss+11,by omega,
    actualPrincipal_oneHigh_of_compactPlanar (mainPhaseParameters length positive) positive
      originalSeedCenter originalSeedCenter_inside originalSeedCenter originalSeedCenter_inside originalSeedCenter_zero
      outer smooth compact (mainPhaseParameters_widthHalf length positive) (mainPhaseParameters_widthLength length positive)
      higher higherLarge shift loss lossLarge lowFits estimate⟩

end Grad.OriginalMainConsumer
