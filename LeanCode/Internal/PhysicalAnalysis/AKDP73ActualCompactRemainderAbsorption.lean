import AKDP72CompactBesselLowerGraphNorm
import AKDP1ActualL2TensorRemainder
import AKDM4SecondTensorRemainderAbsorption

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
open Set
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets Grad.TensorBootstrap
open Grad.WeightedJets.Ordered Grad.WeightedJets.ZeroExtension

/-- The checked whole-plane first absorption applies directly to the
literal compact equation, with its signed Bessel remainder and actual L2
second-tensor difference. -/
theorem startupCompact_actualRemainder_absorption {rank : ℕ} {inside : Set Spatial}
    (data : StartupCompactSpatialEquation rank inside) (closed : IsClosed inside)
    (localizer : TestLocalizer openUnitDisk inside)
    (outer : Spatial → ℝ) (smooth : ContDiff ℝ ∞ outer) (compact : HasCompactSupport outer)
    (operators : Fin 2 → Fin 2 → StartupRankOperator rank 3 3)
    (small : ‖startupOrderedSecondSum rank (fun index => (operators index.1 index.2).localizedCoarse outer smooth compact)‖≤(1/8 : ℝ)) :
    ‖orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl data.field‖≤(8/7 : ℝ)*
      (‖startupCompactBesselRemainder data‖+
        ∑ index : TensorIndex,‖startupActualRankTensorRemainder data outer smooth compact operators index‖) := by
  let original := hilbertLift startupPlaneExtension (orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl data.field)
  let zeroth := hilbertLift startupPlaneExtension (orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl data.zeroth)
  let flux := fun direction => -(hilbertLift startupPlaneExtension (orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl (data.flux direction)))
  have equation (word : DerivativeIndex rank) := startupActualRankTensorRemainder_equation data closed localizer outer smooth compact operators word
  have actual := startupOrdered_fullRemainder_absorption rank
    (fun index => (operators index.1 index.2).localizedCoarse outer smooth compact) small original zeroth flux
    (startupActualRankTensorRemainder data outer smooth compact operators) (fun word => by
      change Laplacian.laplacian (distributionEmbedding (original word)) = _
      simp only [map_add,Finset.sum_add_distrib]
      have same := equation word
      simpa only [original,zeroth,flux,PiLp.neg_apply,map_neg,Finset.sum_neg_distrib,sub_eq_add_neg] using same)
  have extensionNorm : ‖original‖=‖orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl data.field‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [original,PiLp.norm_sq_eq_of_L2,hilbertLift_apply,startupPlaneExtension_norm]
  rw [extensionNorm] at actual
  exact actual

end Grad.CartesianStartup
