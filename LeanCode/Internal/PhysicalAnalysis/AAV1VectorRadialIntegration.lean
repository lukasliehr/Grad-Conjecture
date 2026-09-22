import AAR27ExactPhysicalConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularConverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.AnnularReconstruction Grad.GaugeCoefficients.Physical.WeightedTrace

theorem collarContinuous_inner (dimension : ℕ) (lower : ℝ) (bounded : lower ≤ 1)
    (test field : C(ℝ, ComplexEuclidean dimension)) :
    inner ℂ (collarContinuousL2 (ComplexEuclidean dimension) lower test)
      (collarContinuousL2 (ComplexEuclidean dimension) lower field) =
      ∫ radius in lower..1, inner ℂ (test radius) (field radius) := by
  rw [L2.inner_def, intervalIntegral.integral_of_le bounded, ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [(collarContinuous_memLp (ComplexEuclidean dimension) lower test).coeFn_toLp,
    (collarContinuous_memLp (ComplexEuclidean dimension) lower field).coeFn_toLp]
    with radius testLaw fieldLaw
  change collarContinuousL2 (ComplexEuclidean dimension) lower test radius = _ at testLaw
  change collarContinuousL2 (ComplexEuclidean dimension) lower field radius = _ at fieldLaw
  rw [testLaw, fieldLaw]

/-- Vector-valued smooth tests against the same genuine completed radial graph.
This is the endpoint formula needed for the full finite-core converse. -/
theorem weightedRadial_vector_parts (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : WeightedRadialH1 dimension lower)
    (test : complexSmoothRadialCore dimension) :
    inner ℂ (collarContinuousL2 (ComplexEuclidean dimension) lower test.val.2)
      (collarH1Coordinate (ComplexEuclidean dimension) lower 0
        (weightedToOrdinary dimension lower positive bounded.le field)) +
    inner ℂ (collarContinuousL2 (ComplexEuclidean dimension) lower test.val.1)
      (collarH1Coordinate (ComplexEuclidean dimension) lower 1
        (weightedToOrdinary dimension lower positive bounded.le field)) =
      inner ℂ (test.val.1 1) (weightedRadialTrace dimension lower positive bounded 1 field) -
        inner ℂ (test.val.1 lower) (weightedRadialTrace dimension lower positive bounded 0 field) := by
  let valueMap := (collarH1Coordinate (ComplexEuclidean dimension) lower 0).comp
    (weightedToOrdinary dimension lower positive bounded.le)
  let slopeMap := (collarH1Coordinate (ComplexEuclidean dimension) lower 1).comp
    (weightedToOrdinary dimension lower positive bounded.le)
  let valueTest := collarContinuousL2 (ComplexEuclidean dimension) lower test.val.1
  let slopeTest := collarContinuousL2 (ComplexEuclidean dimension) lower test.val.2
  have leftContinuous : Continuous (fun field : WeightedRadialH1 dimension lower =>
      inner ℂ slopeTest (valueMap field) + inner ℂ valueTest (slopeMap field)) :=
    ((innerSL ℂ slopeTest).continuous.comp valueMap.continuous).add
      ((innerSL ℂ valueTest).continuous.comp slopeMap.continuous)
  have rightContinuous : Continuous (fun field : WeightedRadialH1 dimension lower =>
      inner ℂ (test.val.1 1) (weightedRadialTrace dimension lower positive bounded 1 field) -
        inner ℂ (test.val.1 lower) (weightedRadialTrace dimension lower positive bounded 0 field)) :=
    ((innerSL ℂ (test.val.1 1)).continuous.comp
      (weightedRadialTrace dimension lower positive bounded 1).continuous).sub
      ((innerSL ℂ (test.val.1 lower)).continuous.comp
        (weightedRadialTrace dimension lower positive bounded 0).continuous)
  apply isClosed_property (weightedRadialCoreInto_denseRange dimension lower)
    (isClosed_eq leftContinuous rightContinuous) _ field
  intro core
  dsimp only [valueMap, slopeMap, valueTest, slopeTest, ContinuousLinearMap.comp_apply]
  rw [weightedToOrdinary_core, collarH1Coordinate_core_zero, collarH1Coordinate_core_one,
    weightedRadialTrace_core, weightedRadialTrace_core,
    collarContinuous_inner dimension lower bounded.le, collarContinuous_inner dimension lower bounded.le]
  change (∫ radius in lower..1, inner ℂ (test.val.2 radius) (core.val.val.1 radius)) +
    (∫ radius in lower..1, inner ℂ (test.val.1 radius) (core.val.val.2 radius)) =
      inner ℂ (test.val.1 1) (core.val.val.1 1) - inner ℂ (test.val.1 lower) (core.val.val.1 lower)
  rw [← intervalIntegral.integral_add
    ((test.val.2.continuous.inner core.val.val.1.continuous).intervalIntegrable lower 1)
    ((test.val.1.continuous.inner core.val.val.2.continuous).intervalIntegrable lower 1)]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun radius => inner ℂ (test.val.1 radius) (core.val.val.1 radius))
  · intro radius _
    simpa only [add_comm] using (test.property.2 radius).inner ℂ (core.val.property radius)
  · exact ((test.val.2.continuous.inner core.val.val.1.continuous).add
      (test.val.1.continuous.inner core.val.val.2.continuous)).intervalIntegrable lower 1

end Grad.AnnularConverse
