import AKDP73ActualCompactRemainderAbsorption
import AKDP74CompactBesselAdjustableNorm
import AKDP65AbstractTensorRemainderBound
import AKDP70ActualCutoffLowerGraphFormula
import AKDP71ActualPhaseLowerGraphFormula

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets Grad.TensorBootstrap
open Grad.WeightedJets.Ordered Grad.WeightedJets.ZeroExtension

/-- The actual compact equation, its literal Bessel remainder, and its
literal second-tensor difference yield a uniform adjustable top-rank
estimate on one rank-independent coefficient neighborhood. -/
theorem startupGenericCompactRank_estimate {State : Type*} (rank : ℕ) {inside : Set Spatial}
    (closed : IsClosed inside) (localizer : TestLocalizer openUnitDisk inside)
    (outer : Spatial → ℝ) (smooth : ContDiff ℝ ∞ outer) (compact : HasCompactSupport outer)
    (data : State → StartupCompactSpatialEquation rank inside)
    (operators : State → Fin 2 → Fin 2 → StartupRankOperator rank 3 3)
    (small : ∀ state,‖startupOrderedSecondSum rank
      (fun index => (operators state index.1 index.2).localizedCoarse outer smooth compact)‖≤(1/8 : ℝ))
    (high low : State → ℝ)
    (bessel : ∀ epsilon : ℝ,0<epsilon → ∃ constant : ℝ,0≤constant ∧ ∀ state,
      ‖startupCompactBesselRemainder (data state)‖≤epsilon*high state+constant*low state)
    (tensor : ∀ index : TensorIndex,∀ epsilon : ℝ,0<epsilon → ∃ constant : ℝ,0≤constant ∧ ∀ state,
      ‖startupActualRankTensorRemainder (data state) outer smooth compact (operators state) index‖≤epsilon*high state+constant*low state)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ constant : ℝ,0≤constant ∧ ∀ state,
      ‖orderedDerivative 3 rank rank openUnitDisk (fun _ => 0) le_rfl (data state).field‖≤epsilon*high state+constant*low state := by
  let delta := 7*epsilon/40
  have deltaPositive : 0<delta := by positivity
  obtain ⟨besselConstant,besselNonnegative,besselBound⟩ := bessel delta deltaPositive
  choose tensorConstant tensorNonnegative tensorBound using fun index => tensor index delta deltaPositive
  refine ⟨(8/7 : ℝ)*(besselConstant+∑ index,tensorConstant index),
    mul_nonneg (by norm_num) (add_nonneg besselNonnegative (Finset.sum_nonneg (fun index _ => tensorNonnegative index))),?_⟩
  intro state
  have actual := startupCompact_actualRemainder_absorption (data state) closed localizer outer smooth compact (operators state) (small state)
  have tensors := Finset.sum_le_sum (fun index (_ : index∈Finset.univ) => tensorBound index state)
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Finset.sum_mul] at tensors
  norm_num only [Fintype.card_prod,Fintype.card_fin,Nat.cast_ofNat] at tensors
  have paid := actual.trans (mul_le_mul_of_nonneg_left (add_le_add (besselBound state) tensors) (by norm_num : (0 : ℝ)≤8/7))
  dsimp only [delta] at paid
  nlinarith only [paid]

end Grad.CartesianStartup
