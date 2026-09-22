import AKDP1ActualL2TensorRemainder
import AKDP17ActualOriginalRankMatrixRemainder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets Grad.TensorBootstrap
open Grad.WeightedJets.ZeroExtension Grad.WeightedJets.Ordered

/-- Actual outer localization contracts the full L2 tensor difference.
This does not assume support preservation by the rank operator. -/
theorem startupNestedTensorRemainder_norm {rank : ℕ} {inside : Set Spatial}
    (outer : Spatial → ℝ) (smooth : ContDiff ℝ ∞ outer) (compact : HasCompactSupport outer)
    (plateau : ∀ point ∈ inside,outer point=1) (operator : StartupRankOperator rank 3 3)
    (field tensor : Tensor rank (StartupL2 3))
    (supported : ∀ word,SupportedField (CellValues 3) openUnitDisk inside (tensor word)) :
    ‖hilbertLift startupPlaneExtension tensor-
      operator.localizedCoarse outer smooth compact (hilbertLift startupPlaneExtension field)‖ ≤
      ‖startupCutoffL2 outer smooth compact‖*
        ‖startupTensorFieldEquiv 3 rank tensor-operator.coarse (startupTensorFieldEquiv 3 rank field)‖ := by
  let difference := tensor-operator.orderedCoarse field
  have same : hilbertLift startupPlaneExtension tensor-
      operator.localizedCoarse outer smooth compact (hilbertLift startupPlaneExtension field) =
      hilbertLift startupPlaneExtension (hilbertLift (startupCutoffL2 outer smooth compact) difference) := by
    apply PiLp.ext
    intro word
    change startupPlaneExtension (tensor word)-
      operator.localizedCoarse outer smooth compact (hilbertLift startupPlaneExtension field) word =
      startupPlaneExtension (startupCutoffL2 outer smooth compact (tensor word-operator.orderedCoarse field word))
    rw [StartupRankOperator.localizedCoarse_extension,map_sub,map_sub,
      startupCutoff_supported_absorb outer smooth compact plateau _ (supported word)]
  have extended : ‖startupPlaneExtension‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro value
    rw [startupPlaneExtension_norm,one_mul]
  have coarseSame : startupTensorFieldEquiv 3 rank (operator.orderedCoarse field) =
      operator.coarse (startupTensorFieldEquiv 3 rank field) := by
    change startupTensorFieldEquiv 3 rank ((startupTensorFieldEquiv 3 rank).symm _) = _
    exact LinearIsometryEquiv.apply_symm_apply _ _
  rw [same]
  apply (hilbertLift_norm_le startupPlaneExtension extended _).trans
  apply (hilbertLiftLinear_norm_le (startupCutoffL2 outer smooth compact) difference).trans_eq
  apply congrArg (fun value : ℝ => ‖startupCutoffL2 outer smooth compact‖*value)
  rw [← LinearIsometryEquiv.norm_map (startupTensorFieldEquiv 3 rank) difference]
  change ‖startupTensorFieldEquiv 3 rank (tensor-operator.orderedCoarse field)‖ = _
  rw [map_sub,coarseSame]

/-- This bound applies directly to the actual compact-equation remainder
used by the checked whole-plane second-divergence absorption. -/
theorem startupActualRankTensorRemainder_norm {rank : ℕ} {inside : Set Spatial}
    (data : StartupCompactSpatialEquation rank inside) (closed : IsClosed inside)
    (outer : Spatial → ℝ) (smooth : ContDiff ℝ ∞ outer) (compact : HasCompactSupport outer)
    (plateau : ∀ point ∈ inside,outer point=1)
    (operators : Fin 2 → Fin 2 → StartupRankOperator rank 3 3) (index : TensorIndex) :
    ‖startupActualRankTensorRemainder data outer smooth compact operators index‖ ≤
      ‖startupCutoffL2 outer smooth compact‖*
        ‖startupTensorFieldEquiv 3 rank (orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl (data.tensor index.1 index.2))-
          (operators index.1 index.2).coarse
            (startupTensorFieldEquiv 3 rank (orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl data.field))‖ :=
  startupNestedTensorRemainder_norm outer smooth compact plateau (operators index.1 index.2) _ _
    (fun word => startupOrderedDerivative_supported closed (data.tensor index.1 index.2) (data.tensorSupported index.1 index.2) le_rfl word)

end Grad.CartesianStartup
