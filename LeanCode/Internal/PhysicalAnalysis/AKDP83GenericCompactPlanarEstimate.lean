import AKDP82FullGraphFromTopAndLower
import AKDP80NativePreAxialFluxEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets Grad.TensorBootstrap
open Grad.WeightedJets.ZeroExtension

/-- Full pure-planar estimate for the SAME compact spatial equation.
All constants precede the state, the principal uses a common one-eighth
bound, and the known tensor remains under the second divergence in L2. -/
theorem startupGenericCompactPlanar_estimate {State : Type*} (grade : ℕ) {inside : Set Spatial}
    (closed : IsClosed inside) (localizer : TestLocalizer openUnitDisk inside)
    (outer : Spatial → ℝ) (smooth : ContDiff ℝ ∞ outer) (compact : HasCompactSupport outer)
    (data : State → StartupCompactSpatialEquation grade inside)
    (operators : State → Fin 2 → Fin 2 → StartupRankOperator grade 3 3)
    (small : ∀ state,‖startupOrderedSecondSum grade
      (fun index => (operators state index.1 index.2).localizedCoarse outer smooth compact)‖≤(1/8 : ℝ))
    (high low : State → ℝ) (highNonnegative : ∀ state,0≤high state)
    (bessel : ∀ epsilon : ℝ,0<epsilon → ∃ constant : ℝ,0≤constant ∧ ∀ state,
      ‖startupCompactBesselRemainder (data state)‖≤epsilon*high state+constant*low state)
    (tensor : ∀ index : TensorIndex,∀ epsilon : ℝ,0<epsilon → ∃ constant : ℝ,0≤constant ∧ ∀ state,
      ‖startupActualRankTensorRemainder (data state) outer smooth compact (operators state) index‖≤epsilon*high state+constant*low state)
    (lower : StartupAdjustableSpatialGraph (grade-1)
      (fun state => base 3 grade openUnitDisk (fun _ => 0) (data state).field) high low)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ constant : ℝ,0≤constant ∧ ∀ state,‖(data state).field‖≤epsilon*high state+constant*low state := by
  let count : ℝ := Fintype.card (JetIndex grade)
  let lowerWeight : ℝ := ∑ index : JetIndex grade,Real.sqrt ((degree index).factorial : ℝ)
  have countNonnegative : 0≤count := Nat.cast_nonneg _
  have lowerNonnegative : 0≤lowerWeight := Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  let delta := epsilon/(count+lowerWeight+1)
  have deltaPositive : 0<delta := div_pos positive (by positivity)
  obtain ⟨topConstant,topNonnegative,topBound⟩ := startupGenericCompactRank_estimate grade closed localizer outer smooth compact
    data operators small high low bessel tensor delta deltaPositive
  obtain ⟨lowConstant,lowNonnegative,lowBound⟩ := lower delta deltaPositive
  refine ⟨count*topConstant+lowerWeight*lowConstant,
    add_nonneg (mul_nonneg countNonnegative topNonnegative) (mul_nonneg lowerNonnegative lowNonnegative),?_⟩
  intro state
  obtain ⟨graph,graphSame,graphBound⟩ := lowBound state
  have complete := startupFullGraph_top_lower_norm (data state).field graph graphSame.symm
  have paid := complete.trans (add_le_add
    (mul_le_mul_of_nonneg_left (topBound state) countNonnegative)
    (mul_le_mul_of_nonneg_left graphBound lowerNonnegative))
  have allocated : (count+lowerWeight)*delta≤epsilon := by
    have exactDelta : delta*(count+lowerWeight+1)=epsilon := div_mul_cancel₀ epsilon (by positivity)
    nlinarith [deltaPositive]
  have main := mul_le_mul_of_nonneg_right allocated (highNonnegative state)
  nlinarith only [paid,main]

end Grad.CartesianStartup
