import AKDJ3ActualZeroSeedProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3500
open Set Filter
open scoped Topology ContDiff BigOperators
namespace Grad.OriginalInverseNeighborhood
open Grad.CartesianState Grad.Constraints Grad.Q24Realization Grad.PhysicalCoordinates
open Grad.NonlinearQuotientBounds Grad.RealFixedRanges Grad.FinitePhysicalJetLift
open Grad.GaugeCoefficients.Physical.Allocation Grad.OriginalCoreRealization Grad.OriginalZeroSeed
open Grad.SmoothingFamily Grad.NashMoser.OriginalIteration Grad.NashMoser.OriginalLimit

theorem seedSum_le_four_distance (center seed : Seed.Parameters) :
    (∑ coordinate : Fin 4, |seed coordinate-center coordinate|) ≤ 4*dist seed center := by
  calc
    _ ≤ ∑ _coordinate : Fin 4, ‖seed-center‖ := by
      apply Finset.sum_le_sum
      intro coordinate _
      exact norm_le_pi_norm (seed-center) coordinate
    _ = _ := by simp [dist_eq_norm]

/-- A genuine original Newton product with base grade24, constructed from
physical chart continuity. It controls the actual physical B24 on every
state in the low ball, while all higher norms remain unrestricted. -/
theorem actualNewton_product_neighborhood (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain)
    (center : Seed.Parameters) (insideC : center ∈ Seed.parameterDomain) (zeroC : center 0=0)
    (target : ℝ) (positive : 0 < target) :
    ∃ neighborhood : OriginalNewtonNeighborhood parameters reference insideR 24,
      IsOpen neighborhood.parameterDomain ∧ (center,0) ∈ neighborhood.parameterDomain ∧
      (∀ finite ∈ neighborhood.parameterDomain, ∀ coordinate : Fin 4,
        |finite.1 coordinate| ≤ 1+‖center‖) ∧
      ∀ finite (member : finite ∈ neighborhood.parameterDomain)
        (state : stateSmoothRange parameters reference insideR),
        stateSize parameters reference insideR 24 0 state ≤ 2*neighborhood.radius →
        physicalBudget parameters
          (actualFiniteCurrentField parameters reference insideR finite.1
            (neighborhood.patchInside (neighborhood.seedInside finite member)) (finite.2,state))
          (finite.1 0) finite.2 24 < target := by
  obtain ⟨delta,deltaPositive,control⟩ := actualZeroSeed_product parameters reference insideR 24 (by norm_num)
    center insideC zeroC target positive
  let radius := min 1 (delta/16)
  have radiusPositive : 0 < radius := lt_min zero_lt_one (by positivity)
  have radiusSmall : radius ≤ 1 := min_le_left _ _
  have radiusDelta : radius ≤ delta/16 := min_le_right _ _
  have sevenSmall : 7*radius < delta := by linarith
  have stateNorm (state : stateSmoothRange parameters reference insideR) :
      ‖stateSmoothEmbedding parameters reference insideR 24 (by norm_num) state‖ =
        stateSize parameters reference insideR 24 0 state := rfl
  have pointControl (seed : Seed.Parameters) (epsilon : ℝ)
      (state : stateSmoothRange parameters reference insideR)
      (seedClose : dist seed center ≤ radius) (curvature : |epsilon| ≤ radius)
      (stateSmall : stateSize parameters reference insideR 24 0 state ≤ 2*radius) :
      ∃ insideS : seed ∈ Seed.parameterDomain,
      ∃ _axis : ChartAxisCondition (smoothingChartCore parameters state.val),
        physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS (epsilon,state))
          (seed 0) epsilon 24 < target := by
    apply control seed epsilon state
    rw [stateNorm]
    have seedBound := (seedSum_le_four_distance center seed).trans
      (mul_le_mul_of_nonneg_left seedClose (by norm_num : (0:ℝ) ≤ 4))
    linarith
  have zeroSmall : stateSize parameters reference insideR 24 0
      (0 : stateSmoothRange parameters reference insideR) ≤ 2*radius := by
    rw [map_zero]
    positivity
  have patchInside : Metric.closedBall center radius ⊆ Seed.parameterDomain := by
    intro seed close
    exact (pointControl seed 0 0 (Metric.mem_closedBall.mp close)
      (by simpa only [abs_zero] using radiusPositive.le) zeroSmall).choose
  have axis (state : stateSmoothRange parameters reference insideR)
      (small : stateSize parameters reference insideR 24 0 state ≤ 2*radius) :
      ChartAxisCondition (smoothingChartCore parameters state.val) :=
    (pointControl center 0 state (by simpa only [dist_self] using radiusPositive.le)
      (by simpa only [abs_zero] using radiusPositive.le) small).choose_spec.choose
  let neighborhood : OriginalNewtonNeighborhood parameters reference insideR 24 := {
    baseLarge := by norm_num
    parameterDomain := Metric.ball center radius ×ˢ Ioo (-radius) radius
    seedPatch := Metric.closedBall center radius
    compact := isCompact_closedBall center radius
    patchInside := patchInside
    curvatureBound := radius
    seedInside := fun _ member => Metric.mem_closedBall.mpr (Metric.mem_ball.mp member.1).le
    curvature := fun _ member => by
      rw [Real.norm_eq_abs]
      exact (abs_lt.mpr member.2).le
    radius := radius
    radiusPositive := radiusPositive
    radiusSmall := radiusSmall
    axis := axis }
  refine ⟨neighborhood,Metric.isOpen_ball.prod isOpen_Ioo,?_,?_,?_⟩
  · exact ⟨Metric.mem_ball_self radiusPositive,by exact ⟨by linarith, radiusPositive⟩⟩
  · intro finite member coordinate
    have close : dist finite.1 center < radius := member.1
    have normBound : ‖finite.1‖ ≤ 1+‖center‖ := by
      have triangle := norm_le_insert' finite.1 center
      rw [← dist_eq_norm] at triangle
      linarith
    exact (norm_le_pi_norm finite.1 coordinate).trans normBound
  · intro finite member state small
    have result := pointControl finite.1 finite.2 state (Metric.mem_ball.mp member.1).le
      (abs_lt.mpr member.2).le small
    exact result.choose_spec.choose_spec

end Grad.OriginalInverseNeighborhood
