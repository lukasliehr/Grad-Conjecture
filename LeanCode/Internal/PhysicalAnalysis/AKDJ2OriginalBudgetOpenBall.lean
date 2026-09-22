import AKDJ1ActualCompletedBudget
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3500
open Set Filter
open scoped Topology ContDiff BigOperators
namespace Grad.OriginalInverseNeighborhood
open Grad.CartesianState Grad.Constraints Grad.Q24Realization Grad.PhysicalCoordinates
open Grad.NonlinearQuotientBounds Grad.RealFixedRanges Grad.FinitePhysicalJetLift
open Grad.GaugeCoefficients.Physical.Allocation Grad.OriginalCoreRealization
open Grad.ImplementationReadiness Grad.SmoothingFamily

/-- A strict actual physical budget at one original core gives an open
ball in a single original finite grade. Higher norms are unrestricted. -/
theorem actualPhysicalBudget_open_ball (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (center : RealMixedCore parameters reference insideR)
    (seedInside : center.1 ∈ Seed.parameterDomain)
    (axis : ChartAxisCondition (smoothingChartCore parameters center.2.2.val))
    (target : ℝ)
    (small : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR center.1 seedInside center.2)
      (center.1 0) center.2.1 grade < target) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ point : RealMixedAmbient parameters reference insideR grade large,
      dist point (realMixedCoreEmbed parameters reference insideR grade large center) < radius →
      point ∈ realMixedDomain parameters reference insideR grade large ∧
      completedPhysicalBudget parameters reference grade
        (realMixedInclusion parameters reference insideR grade large point) < target := by
  let centerPoint := realMixedCoreEmbed parameters reference insideR grade large center
  have centerInside : centerPoint ∈ realMixedDomain parameters reference insideR grade large :=
    (realMixedDomain_core_iff parameters reference insideR grade large center).2 ⟨seedInside,axis⟩
  have continuity : ContinuousAt (fun point : RealMixedAmbient parameters reference insideR grade large =>
      completedPhysicalBudget parameters reference grade
        (realMixedInclusion parameters reference insideR grade large point)) centerPoint :=
    ((completedPhysicalBudget_continuousOn parameters reference grade).continuousAt
      ((mixedDomain_isOpen parameters grade).mem_nhds centerInside)).comp
      (realMixedInclusion parameters reference insideR grade large).continuous.continuousAt
  have centerSmall : completedPhysicalBudget parameters reference grade
      (realMixedInclusion parameters reference insideR grade large centerPoint) < target := by
    dsimp only [centerPoint]
    rw [realMixedInclusion_core,completedPhysicalBudget_core parameters reference insideR grade center.1 seedInside center.2 axis]
    exact small
  have neighborhood := Filter.inter_mem
    ((realMixedDomain_isOpen parameters reference insideR grade large).mem_nhds centerInside)
    (continuity.eventually (gt_mem_nhds centerSmall))
  obtain ⟨radius,positive,included⟩ := Metric.mem_nhds_iff.mp neighborhood
  exact ⟨radius,positive,fun point close => included close⟩

/-- Exact product distance from a zero-state seed, with the original sum
norm and all four seed coordinates. -/
theorem realMixedCore_distance_zero (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (center seed : Seed.Parameters) (epsilon : ℝ) (state : stateSmoothRange parameters reference insideR) :
    dist (realMixedCoreEmbed parameters reference insideR grade large (seed,epsilon,state))
      (realMixedCoreEmbed parameters reference insideR grade large (center,0,0)) =
      (∑ coordinate : Fin 4, |seed coordinate-center coordinate|)+|epsilon|+
        ‖stateSmoothEmbedding parameters reference insideR grade large state‖ := by
  rw [dist_eq_norm,WithLp.prod_norm_eq_of_L1]
  change ‖(WithLp.toLp 1 seed : SeedL1)-(WithLp.toLp 1 center : SeedL1)‖+
    ‖realJointCoreEmbed parameters reference insideR grade large (epsilon,state)-
      realJointCoreEmbed parameters reference insideR grade large (0,0)‖ = _
  have zero : realJointCoreEmbed parameters reference insideR grade large (0,0) = 0 := by
    change WithLp.toLp 1 ((0:ℝ),stateSmoothEmbedding parameters reference insideR grade large 0)=0
    rw [map_zero]
    rfl
  rw [zero,sub_zero,Grad.SmoothForward.realJointCoreEmbed_norm]
  have finite : ‖(WithLp.toLp 1 seed : SeedL1)-(WithLp.toLp 1 center : SeedL1)‖ =
      ∑ coordinate : Fin 4, |seed coordinate-center coordinate| := by
    rw [PiLp.norm_eq_of_L1]
    simp only [PiLp.sub_apply,Real.norm_eq_abs]
  rw [finite]
  ring

end Grad.OriginalInverseNeighborhood
