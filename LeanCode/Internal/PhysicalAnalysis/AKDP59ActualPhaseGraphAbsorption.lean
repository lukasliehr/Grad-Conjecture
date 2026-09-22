import AKDP46ActualPhaseCoordinateAbsorption

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets
open Grad.WeightedJets.SpatialMultiplier Grad.ActualOriginalSourceMoments Grad.OriginalCartesianTameEstimate
namespace StartupCellSpatialSymbol

/-- Full lower spatial graph norm of the actual phase product, with
all coordinates absorbed against the same original endpoints. -/
theorem graph_adjustable {order reserve : ℕ}
    (symbol : StartupCellSpatialSymbol order reserve) (parameters : PhaseParameters)
    (grade cost : ℕ) (costPositive : 0<cost) (allocated : order+cost≤grade)
    (constant : JetIndex order → ℝ) (nonnegative : ∀ index,0≤constant index)
    (sharp : ∀ index cell point,|scalarDerivative index.val (symbol.toFun cell) point|≤
      constant index*cellFrequency cell^(degree index+cost))
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ remainder : ℝ,0≤remainder ∧ ∀ (dimension : ℕ) (core : ACore parameters dimension)
      (input : GraphGrade dimension order reserve openUnitDisk) (output : GraphGrade dimension order 0 openUnitDisk),
      base dimension order openUnitDisk (fun _ => reserve) input=(originalSourceMoments parameters core).field →
      base dimension order openUnitDisk (fun _ => 0) output=symbol.baseField input →
      ‖output‖≤epsilon*originalPlanarNorm parameters grade core+remainder*originalCellNorm parameters grade core := by
  classical
  let count : ℝ := Fintype.card (JetIndex order)
  have countNonnegative : 0≤count := Nat.cast_nonneg _
  let delta := epsilon/(count+1)
  have deltaPositive : 0<delta := div_pos positive (by positivity)
  have each (index : JetIndex order) := symbol.coordinateField_adjustable parameters index grade cost costPositive
    (by have bounded := index.property; change degree index≤order at bounded; omega)
    constant nonnegative sharp delta deltaPositive
  choose remainders remainderNonnegative estimates using each
  refine ⟨∑ index,remainders index,Finset.sum_nonneg (fun index _ => remainderNonnegative index),?_⟩
  intro dimension core input output sameInput sameOutput
  have outputSame : output=symbol.graph input := by
    apply base_injective dimension order openUnitDisk openUnitDisk_isOpen (fun _ => 0)
    rw [sameOutput,symbol.graph_base]
  rw [outputSame]
  have finite := startupFiniteHilbert_norm_le_sum (fun index : JetIndex order => (symbol.graph input).val index)
  change ‖symbol.graph input‖≤_ at finite
  apply (finite.trans (Finset.sum_le_sum (fun index _ => estimates index dimension core input sameInput))).trans
  rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,←Finset.sum_mul]
  have main : count*delta≤epsilon := by
    have exactCount : delta*(count+1)=epsilon := div_mul_cancel₀ epsilon (by positivity)
    nlinarith [deltaPositive]
  apply add_le_add_left
  simp only [Finset.card_univ]
  change count*(delta*originalPlanarNorm parameters grade core)≤epsilon*originalPlanarNorm parameters grade core
  rw [←mul_assoc]
  exact mul_le_mul_of_nonneg_right main (Real.sqrt_nonneg _)

end StartupCellSpatialSymbol
end Grad.CartesianStartup
