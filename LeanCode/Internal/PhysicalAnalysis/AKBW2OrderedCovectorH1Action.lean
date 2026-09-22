import AKBW1CoupledTensorResolvent
import TensorLiftProofConsumer
import WC2ProofConsumer
import GTProof

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.TensorBootstrap Grad.TensorCoefficients
open Grad.WeakPullback.H1

/-- Genuine rank-covector lift on the existing H1 graph. The extra covector
indices rotate as well as the physical argument; its norm is one at every rank. -/
def startupOrderedPullbackH1 (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) :
    StartupOrderedH1 rank ≃ₗᵢ[ℂ] StartupOrderedH1 rank :=
  (LinearIsometryEquiv.piLpCongrRight 2
    (fun _ : DerivativeIndex rank => h1Pullback orthogonal)).trans
      (Grad.TensorAction.Generic.covectorEquivalence FieldH1 rank orthogonal)

theorem startupOrderedPullbackH1_value (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : StartupOrderedH1 rank) :
    startupOrderedValue rank (startupOrderedPullbackH1 rank orthogonal field) =
      Grad.TensorLift.tensorLift rank orthogonal (startupOrderedValue rank field) := by
  apply PiLp.ext
  intro word
  change valueInclusion (∑ input : DerivativeIndex rank,
      ((∏ position : Fin rank, orthogonal (spatialDirection (word position)) (input position) : ℝ) : ℂ) •
        h1Pullback orthogonal (field input)) =
    ∑ input : DerivativeIndex rank,
      (∏ position : Fin rank, orthogonal (spatialDirection (word position)) (input position)) •
        Grad.KernelPullback.orthogonalPullback orthogonal (valueInclusion (field input))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro input _
  rw [map_smul, valueInclusion_h1Pullback]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_eq_complex_ofReal]

theorem startupOrderedPullbackH1_norm (rank : ℕ) (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial)
    (field : StartupOrderedH1 rank) :
    ‖startupOrderedPullbackH1 rank orthogonal field‖ = ‖field‖ :=
  (startupOrderedPullbackH1 rank orthogonal).norm_map field

end Grad.CartesianStartup
