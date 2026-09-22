import AKDP42ActualPhasePieceMixedNorm
import AKDP43FiniteMixedOrderAbsorption

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets
open Grad.WeightedJets.SpatialMultiplier Grad.ActualOriginalSourceMoments Grad.OriginalCartesianTameEstimate
namespace StartupCellSpatialSymbol

/-- Every genuine positive-cost phase product is adjustable in the
original planar endpoint. Its remaining norm is purely in the cells. -/
theorem coordinateField_adjustable {order reserve : ℕ}
    (symbol : StartupCellSpatialSymbol order reserve) (parameters : PhaseParameters)
    (upper : JetIndex order) (grade cost : ℕ) (costPositive : 0<cost)
    (allocated : degree upper+cost≤grade)
    (constant : JetIndex order → ℝ) (nonnegative : ∀ index,0≤constant index)
    (sharp : ∀ index cell point,|scalarDerivative index.val (symbol.toFun cell) point|≤
      constant index*cellFrequency cell^(degree index+cost))
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ remainder : ℝ,0≤remainder ∧ ∀ (dimension : ℕ) (core : ACore parameters dimension)
      (field : GraphGrade dimension order reserve openUnitDisk),
      base dimension order openUnitDisk (fun _ => reserve) field=(originalSourceMoments parameters core).field →
      ‖symbol.coordinateField field upper‖≤epsilon*originalPlanarNorm parameters grade core+
        remainder*originalCellNorm parameters grade core := by
  classical
  let Indices := {lower : JetIndex order // lower∈below upper}
  have strict (lower : Indices) : degree lower.val<grade := by
    have included := (mem_below upper lower.val).mp lower.property
    rcases included with ⟨first,second⟩
    change upper.val.1+upper.val.2+cost≤grade at allocated
    change lower.val.val.1+lower.val.val.2<grade
    omega
  let weights := fun lower : Indices => (binomial upper lower.val : ℝ)*constant (difference upper lower.val)
  obtain ⟨remainder,remainderNonnegative,bound⟩ := startupFiniteMixedOrders_adjustable grade
    (fun lower : Indices => degree lower.val) strict weights
    (fun lower => mul_nonneg (Nat.cast_nonneg _) (nonnegative _)) epsilon positive
  refine ⟨remainder,remainderNonnegative,?_⟩
  intro dimension core field same
  apply (symbol.coordinateField_mixedNorm parameters core field same upper grade cost allocated constant nonnegative sharp).trans
  have actual := bound dimension parameters core
  change (∑ lower ∈ (below upper).attach,
    (binomial upper lower.val : ℝ)*constant (difference upper lower.val)*
      originalMixedOrderNorm parameters grade (degree lower.val) core)≤_ at actual
  rw [Finset.sum_attach (below upper) (fun lower =>
    (binomial upper lower : ℝ)*constant (difference upper lower)*
      originalMixedOrderNorm parameters grade (degree lower) core)] at actual
  exact actual

end StartupCellSpatialSymbol

theorem startupPhaseSlopeCoordinate_adjustable (parameters : PhaseParameters) (scale : ℝ)
    (scaleNonnegative : 0≤scale) (order grade : ℕ) (upper : JetIndex order)
    (allocated : degree upper+1≤grade) (direction : Fin 2) (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ remainder : ℝ,0≤remainder ∧ ∀ (dimension : ℕ) (core : ACore parameters dimension)
      (field : GraphGrade dimension order (order+1) openUnitDisk),
      base dimension order openUnitDisk (fun _ => order+1) field=(originalSourceMoments parameters core).field →
      ‖(startupPhaseSlopeSymbol parameters.sigma0 parameters.gamma scale parameters.gamma_pos.le scaleNonnegative order direction).coordinateField field upper‖≤
        epsilon*originalPlanarNorm parameters grade core+remainder*originalCellNorm parameters grade core :=
  StartupCellSpatialSymbol.coordinateField_adjustable _ parameters upper grade 1 (by norm_num) allocated
    (fun index => startupPhaseDerivativeConstant parameters.gamma scale (degree index+1))
    (fun index => startupPhaseDerivativeConstant_nonnegative _ _ parameters.gamma_pos.le scaleNonnegative _)
    (fun index cell point => startupPhaseSlope_scalar_bound parameters.sigma0 parameters.gamma scale
      parameters.gamma_pos.le scaleNonnegative index cell direction point) epsilon positive

theorem startupPhaseSecondCoordinate_adjustable (parameters : PhaseParameters) (scale : ℝ)
    (scaleNonnegative : 0≤scale) (order grade : ℕ) (upper : JetIndex order)
    (allocated : degree upper+2≤grade) (outer inner : Fin 2) (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ remainder : ℝ,0≤remainder ∧ ∀ (dimension : ℕ) (core : ACore parameters dimension)
      (field : GraphGrade dimension order (order+2) openUnitDisk),
      base dimension order openUnitDisk (fun _ => order+2) field=(originalSourceMoments parameters core).field →
      ‖(startupPhaseSecondSymbol parameters.sigma0 parameters.gamma scale parameters.gamma_pos.le scaleNonnegative order outer inner).coordinateField field upper‖≤
        epsilon*originalPlanarNorm parameters grade core+remainder*originalCellNorm parameters grade core :=
  StartupCellSpatialSymbol.coordinateField_adjustable _ parameters upper grade 2 (by norm_num) allocated
    (fun index => startupPhaseDerivativeConstant parameters.gamma scale (degree index+2)+
      startupPhaseProductConstant parameters.gamma scale index)
    (fun index => add_nonneg
      (startupPhaseDerivativeConstant_nonnegative _ _ parameters.gamma_pos.le scaleNonnegative _)
      (startupPhaseProductConstant_nonnegative _ _ parameters.gamma_pos.le scaleNonnegative index))
    (fun index cell point => startupPhaseSecond_scalar_bound parameters.sigma0 parameters.gamma scale
      parameters.gamma_pos.le scaleNonnegative index cell outer inner point) epsilon positive

end Grad.CartesianStartup
