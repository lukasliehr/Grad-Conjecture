import AKCX48ActualNestedRankDistribution

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.ZeroExtension Grad.WeightedJets.Ordered Grad.TensorBootstrap

private theorem sumMap_remainder {Index Value Target : Type*} [Fintype Index]
    [AddCommGroup Value] [AddCommGroup Target]
    (action : Index → Value →+ Target) (original leading : Index → Value) :
    (∑ index, action index (original index)) =
      (∑ index, action index (leading index))+
      ∑ index, action index (original index-leading index) := by
  simp only [map_sub,Finset.sum_sub_distrib]
  abel

/-- The literal differentiated tensor minus its actual localized leading
operator. It stays in L2, before the regularity proof moves its derivative
into the flux. -/
def startupActualRankTensorRemainder {rank : ℕ} {inside : Set Spatial}
    (data : StartupCompactSpatialEquation rank inside)
    (outer : Spatial → ℝ) (smooth : ContDiff ℝ ∞ outer) (compact : HasCompactSupport outer)
    (operators : Fin 2 → Fin 2 → StartupRankOperator rank 3 3) (index : TensorIndex) :
    StartupOrderedL2 rank :=
  hilbertLift startupPlaneExtension
      (orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl (data.tensor index.1 index.2)) -
    (operators index.1 index.2).localizedCoarse outer smooth compact
      (hilbertLift startupPlaneExtension (orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl data.field))

/-- Exact whole-plane differentiated equation with the SAME tensor
remainder left under two derivatives. No first-graph norm is required. -/
theorem startupActualRankTensorRemainder_equation {rank : ℕ} {inside : Set Spatial}
    (data : StartupCompactSpatialEquation rank inside) (closed : IsClosed inside)
    (localizer : TestLocalizer openUnitDisk inside)
    (outer : Spatial → ℝ) (smooth : ContDiff ℝ ∞ outer) (compact : HasCompactSupport outer)
    (operators : Fin 2 → Fin 2 → StartupRankOperator rank 3 3)
    (word : DerivativeIndex rank) :
    Laplacian.laplacian (distributionEmbedding (hilbertLift startupPlaneExtension
      (orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl data.field) word)) =
      (∑ index : TensorIndex, distributionDerivative index.1 (distributionDerivative index.2
        (distributionEmbedding ((operators index.1 index.2).localizedCoarse outer smooth compact
          (hilbertLift startupPlaneExtension (orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl data.field)) word))))+
      (∑ index : TensorIndex, distributionDerivative index.1 (distributionDerivative index.2
        (distributionEmbedding (startupActualRankTensorRemainder data outer smooth compact operators index word))))+
      distributionEmbedding (hilbertLift startupPlaneExtension
        (orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl data.zeroth) word)-
      ∑ direction : Fin 2, distributionDerivative direction (distributionEmbedding
        (hilbertLift startupPlaneExtension (orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl (data.flux direction)) word)) := by
  let original := fun index : TensorIndex =>
    startupPlaneExtension (orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl (data.tensor index.1 index.2) word)
  let leading := fun index : TensorIndex =>
    (operators index.1 index.2).localizedCoarse outer smooth compact
      (hilbertLift startupPlaneExtension (orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl data.field)) word
  let action := fun index : TensorIndex =>
    (distributionDerivative index.1).toAddMonoidHom.comp
      ((distributionDerivative index.2).toAddMonoidHom.comp distributionEmbedding.toAddMonoidHom)
  have total := sumMap_remainder action original leading
  change (∑ index : TensorIndex, distributionDerivative index.1 (distributionDerivative index.2 (distributionEmbedding (original index)))) =
    (∑ index : TensorIndex, distributionDerivative index.1 (distributionDerivative index.2 (distributionEmbedding (leading index))))+
    ∑ index : TensorIndex, distributionDerivative index.1 (distributionDerivative index.2
      (distributionEmbedding (startupActualRankTensorRemainder data outer smooth compact operators index word))) at total
  have equation := data.differentiated_distribution closed localizer le_rfl word
  change Laplacian.laplacian (distributionEmbedding (startupPlaneExtension _)) = _
  rw [equation]
  rw [Fintype.sum_prod_type] at total
  change (∑ one, ∑ two, distributionDerivative one (distributionDerivative two
    (distributionEmbedding (startupPlaneExtension (orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl (data.tensor one two) word))))) = _ at total
  rw [total]
  rfl

end Grad.CartesianStartup
