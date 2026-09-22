import AEG11ExactEnergyPacketConsumer
import AAV1VectorRadialIntegration
import AHW28LiteralMeanFreePhysicalRV

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularCircularForm
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularConverse Grad.AnnularReconstruction
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Full two-sided completed radial integration by parts, with both actual endpoints. -/
theorem weightedRadial_completed_parts (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (test field : WeightedRadialH1 dimension lower) :
    let ordinary := weightedToOrdinary dimension lower positive bounded.le
    inner ℂ (collarH1Coordinate (ComplexEuclidean dimension) lower 1 (ordinary test))
      (collarH1Coordinate (ComplexEuclidean dimension) lower 0 (ordinary field)) +
    inner ℂ (collarH1Coordinate (ComplexEuclidean dimension) lower 0 (ordinary test))
      (collarH1Coordinate (ComplexEuclidean dimension) lower 1 (ordinary field)) =
    inner ℂ (weightedRadialTrace dimension lower positive bounded 1 test)
      (weightedRadialTrace dimension lower positive bounded 1 field) -
    inner ℂ (weightedRadialTrace dimension lower positive bounded 0 test)
      (weightedRadialTrace dimension lower positive bounded 0 field) := by
  let valueMap := (collarH1Coordinate (ComplexEuclidean dimension) lower 0).comp
    (weightedToOrdinary dimension lower positive bounded.le)
  let slopeMap := (collarH1Coordinate (ComplexEuclidean dimension) lower 1).comp
    (weightedToOrdinary dimension lower positive bounded.le)
  have leftContinuous : Continuous (fun test : WeightedRadialH1 dimension lower =>
      inner ℂ (slopeMap test) (valueMap field) + inner ℂ (valueMap test) (slopeMap field)) :=
    (slopeMap.continuous.inner continuous_const).add (valueMap.continuous.inner continuous_const)
  have rightContinuous : Continuous (fun test : WeightedRadialH1 dimension lower =>
      inner ℂ (weightedRadialTrace dimension lower positive bounded 1 test)
        (weightedRadialTrace dimension lower positive bounded 1 field) -
      inner ℂ (weightedRadialTrace dimension lower positive bounded 0 test)
        (weightedRadialTrace dimension lower positive bounded 0 field)) :=
    ((weightedRadialTrace dimension lower positive bounded 1).continuous.inner continuous_const).sub
      ((weightedRadialTrace dimension lower positive bounded 0).continuous.inner continuous_const)
  apply isClosed_property (weightedRadialCoreInto_denseRange dimension lower)
    (isClosed_eq leftContinuous rightContinuous) _ test
  intro core
  dsimp only [valueMap, slopeMap, ContinuousLinearMap.comp_apply]
  rw [weightedToOrdinary_core, collarH1Coordinate_core_one, collarH1Coordinate_core_zero,
    weightedRadialTrace_core, weightedRadialTrace_core]
  exact weightedRadial_vector_parts dimension lower positive bounded field (acceptedCoreToComplex dimension core)

end Grad.AnnularCircularForm
