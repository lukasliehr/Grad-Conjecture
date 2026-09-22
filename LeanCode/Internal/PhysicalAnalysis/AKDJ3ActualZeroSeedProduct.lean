import AKDJ2OriginalBudgetOpenBall
import AKDI7ZeroEccentricityCurrent
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3500
open Set Filter
open scoped Topology ContDiff BigOperators
namespace Grad.OriginalInverseNeighborhood
open Grad.CartesianState Grad.Constraints Grad.Q24Realization Grad.PhysicalCoordinates
open Grad.NonlinearQuotientBounds Grad.RealFixedRanges Grad.FinitePhysicalJetLift
open Grad.GaugeCoefficients.Physical.Allocation Grad.OriginalCoreRealization Grad.OriginalZeroSeed
open Grad.SmoothingFamily

/-- Actual original low-product neighborhood around a zero-eccentricity
seed. It provides both the chart domain and physical budget, without an
assumed small-chart estimate. -/
theorem actualZeroSeed_product (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (center : Seed.Parameters) (insideC : center ∈ Seed.parameterDomain) (zeroC : center 0=0)
    (target : ℝ) (positive : 0 < target) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ (seed : Seed.Parameters) (epsilon : ℝ)
      (state : stateSmoothRange parameters reference insideR),
      (∑ coordinate : Fin 4, |seed coordinate-center coordinate|)+|epsilon|+
        ‖stateSmoothEmbedding parameters reference insideR grade large state‖ < radius →
      ∃ insideS : seed ∈ Seed.parameterDomain,
      ∃ _axis : ChartAxisCondition (smoothingChartCore parameters state.val),
        physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS (epsilon,state))
          (seed 0) epsilon grade < target := by
  have axisZero : ChartAxisCondition (smoothingChartCore parameters
      (0 : stateSmoothRange parameters reference insideR).val) := by
    change ChartAxisCondition (smoothingChartCore parameters (0 : StateCore parameters))
    rw [smoothingChartCore_zero]
    exact zeroChart_axis
  have small : physicalBudget parameters
      (actualFiniteCurrentField parameters reference insideR center insideC (0,0)) (center 0) 0 grade < target := by
    rw [actualFiniteCurrentBudget_zero reference insideR center insideC zeroC]
    exact positive
  obtain ⟨radius,radiusPositive,control⟩ := actualPhysicalBudget_open_ball parameters reference insideR grade large
    (center,0,0) insideC axisZero target small
  refine ⟨radius,radiusPositive,fun seed epsilon state close => ?_⟩
  have distance : dist (realMixedCoreEmbed parameters reference insideR grade large (seed,epsilon,state))
      (realMixedCoreEmbed parameters reference insideR grade large (center,0,0)) < radius := by
    rw [realMixedCore_distance_zero]
    exact close
  have result := control (realMixedCoreEmbed parameters reference insideR grade large (seed,epsilon,state)) distance
  have inside := (realMixedDomain_core_iff parameters reference insideR grade large (seed,epsilon,state)).1 result.1
  refine ⟨inside.1,inside.2,?_⟩
  have budget := result.2
  rw [realMixedInclusion_core,completedPhysicalBudget_core parameters reference insideR grade seed inside.1 (epsilon,state) inside.2] at budget
  exact budget

end Grad.OriginalInverseNeighborhood
