import WC3Proof

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000

open LineDeriv

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.WeakPullback

/-- Moving an input derivative through the actual pullback uses the
 inverse orthogonal covector, including its literal direction entries. -/
theorem startupPullback_inputDerivative (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (direction : Fin 2) (distribution : FieldDistribution) :
    distributionPullback orthogonal (distributionDerivative direction distribution) =
      ∑ coordinate : Fin 2, orthogonal.symm (spatialDirection direction) coordinate •
        distributionDerivative coordinate (distributionPullback orthogonal distribution) := by
  have covariance := Grad.WeakPullback.directional orthogonal
    (orthogonal.symm (spatialDirection direction)) distribution
  rw [LinearIsometryEquiv.apply_symm_apply] at covariance
  exact covariance.symm.trans (Grad.WeakPullback.Ordered.directional_coordinates
    (orthogonal.symm (spatialDirection direction)) (distributionPullback orthogonal distribution))

/-- The mixed second-order expression is exactly a finite divergence
 tensor with the true inverse covector. No derivative is discarded. -/
theorem startupPullback_mixedDerivative (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (outer inner : Fin 2) (distribution : FieldDistribution) :
    distributionDerivative outer
      (distributionPullback orthogonal (distributionDerivative inner distribution)) =
      ∑ coordinate : Fin 2, orthogonal.symm (spatialDirection inner) coordinate •
        distributionDerivative outer
          (distributionDerivative coordinate (distributionPullback orthogonal distribution)) := by
  rw [startupPullback_inputDerivative, map_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  exact (distributionDerivative outer).toLinearMap.map_smul_of_tower
    (orthogonal.symm (spatialDirection inner) coordinate)
    (distributionDerivative coordinate (distributionPullback orthogonal distribution))

end Grad.CartesianStartup
