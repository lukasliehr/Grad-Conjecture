import AKDP41ActualCellProductMixedNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets
open Grad.WeightedJets.SpatialMultiplier Grad.ActualOriginalSourceMoments Grad.OriginalCartesianTameEstimate
namespace StartupCellSpatialSymbol

/-- The actual stored phase Leibniz piece uses its own cell cost, not the
larger reserve used only to construct the entire graph. -/
theorem piece_mixedNorm {dimension order reserve : ℕ}
    (symbol : StartupCellSpatialSymbol order reserve) (parameters : PhaseParameters)
    (core : ACore parameters dimension) (field : GraphGrade dimension order reserve openUnitDisk)
    (same : base dimension order openUnitDisk (fun _ => reserve) field=(originalSourceMoments parameters core).field)
    (index lower : JetIndex order) (grade moment : ℕ) (allocated : degree lower+moment≤grade)
    (constant : ℝ) (nonnegative : 0≤constant)
    (sharp : ∀ cell point,|scalarDerivative index.val (symbol.toFun cell) point|≤constant*cellFrequency cell^moment) :
    ‖symbol.piece index (field.val lower)‖≤constant*originalMixedOrderNorm parameters grade (degree lower) core := by
  apply startupActualCellProduct_mixedNorm parameters core grade (degree lower) moment allocated (derivativeWord lower)
    (fun cell => scalarDerivative index.val (symbol.toFun cell)) constant nonnegative sharp
    (fun cell => (scalarDerivative_smooth index.val (symbol.toFun cell) (symbol.smooth cell)).continuous.aestronglyMeasurable)
  have actual := symbol.piece_same index lower field
  rw [startupRecoveredDerivative_originalCore parameters core field same lower] at actual
  exact actual

/-- The exact finite phase Leibniz sum retains complementary cell and
spatial orders in every term. -/
theorem coordinateField_mixedNorm {dimension order reserve : ℕ}
    (symbol : StartupCellSpatialSymbol order reserve) (parameters : PhaseParameters)
    (core : ACore parameters dimension) (field : GraphGrade dimension order reserve openUnitDisk)
    (same : base dimension order openUnitDisk (fun _ => reserve) field=(originalSourceMoments parameters core).field)
    (upper : JetIndex order) (grade cost : ℕ) (allocated : degree upper+cost≤grade)
    (constant : JetIndex order → ℝ) (nonnegative : ∀ index,0≤constant index)
    (sharp : ∀ index cell point,|scalarDerivative index.val (symbol.toFun cell) point|≤
      constant index*cellFrequency cell^(degree index+cost)) :
    ‖symbol.coordinateField field upper‖≤
      ∑ lower ∈ below upper,(binomial upper lower : ℝ)*constant (difference upper lower)*
        originalMixedOrderNorm parameters grade (degree lower) core := by
  rw [coordinateField]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro lower included
  rw [norm_smul,Complex.norm_natCast]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply symbol.piece_mixedNorm parameters core field same (difference upper lower) lower grade
    (degree (difference upper lower)+cost) _ _ (nonnegative _) (sharp _)
  have indexes := (mem_below upper lower).mp included
  rcases indexes with ⟨first,second⟩
  change lower.val.1+lower.val.2+((upper.val.1-lower.val.1)+(upper.val.2-lower.val.2)+cost)≤grade
  change upper.val.1+upper.val.2+cost≤grade at allocated
  omega

end StartupCellSpatialSymbol
end Grad.CartesianStartup
