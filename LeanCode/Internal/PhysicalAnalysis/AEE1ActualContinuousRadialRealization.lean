import AEC12ConstructedOriginalYEstimateConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators
namespace Grad.AnnularLowCompletion
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowVolterra
open Grad.AnnularVariational Grad.AnnularSourceGraph
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- A continuous classical derivative and an actual incoming value produce
an element of the accepted radial graph by its completed primitive. -/
def continuousRadialRealization (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (initial : ComplexEuclidean dimension) (derivative : C(ℝ, ComplexEuclidean dimension)) :
    WeightedRadialH1 dimension lower :=
  completedPrimitive dimension lower positive bounded
      (collarContinuousL2 (ComplexEuclidean dimension) lower derivative) +
    weightedRadialCoreInto dimension lower (constantRadialCore dimension initial)

theorem continuousRadialRealization_slope (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (initial : ComplexEuclidean dimension) (derivative : C(ℝ, ComplexEuclidean dimension)) :
    collarH1Coordinate (ComplexEuclidean dimension) lower 1
      (weightedToOrdinary dimension lower positive bounded.le
        (continuousRadialRealization dimension lower positive bounded initial derivative)) =
      collarContinuousL2 (ComplexEuclidean dimension) lower derivative := by
  rw [continuousRadialRealization, map_add, map_add, completedPrimitive_ordinary_slope,
    weightedToOrdinary_core, collarH1Coordinate_core_one, constantRadialCore_slope, map_zero, add_zero]

theorem continuousRadialRealization_section (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (initial : ComplexEuclidean dimension) (derivative : C(ℝ, ComplexEuclidean dimension))
    (radius : Icc lower 1) :
    weightedRadialSection dimension lower positive bounded
      (continuousRadialRealization dimension lower positive bounded initial derivative) radius =
      initial + ∫ point in lower..radius.val, derivative point := by
  rw [continuousRadialRealization, map_add]
  change weightedRadialSection dimension lower positive bounded
      (completedPrimitive dimension lower positive bounded (collarContinuousL2 (ComplexEuclidean dimension) lower derivative)) radius +
    weightedRadialSection dimension lower positive bounded
      (weightedRadialCoreInto dimension lower (constantRadialCore dimension initial)) radius = _
  rw [completedPrimitive_section, ← radialIntervalIntegral_apply, radialIntervalIntegral_core,
    weightedRadialSection_core]
  change (∫ point in lower..radius.val, derivative point) + initial = _
  exact add_comm _ _

theorem continuousRadialRealization_incoming (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (initial : ComplexEuclidean dimension) (derivative : C(ℝ, ComplexEuclidean dimension)) :
    weightedRadialTrace dimension lower positive bounded 0
      (continuousRadialRealization dimension lower positive bounded initial derivative) = initial := by
  rw [← weightedRadialSection_endpoint]
  rw [continuousRadialRealization_section]
  change initial + ∫ point in lower..lower, derivative point = initial
  rw [integral_same, add_zero]

/-- The completed primitive agrees with the actual classical solution on
the entire closed interval; endpoints are determined by the solution. -/
theorem continuousRadialRealization_actual (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (value : ℝ → ComplexEuclidean dimension) (derivative : C(ℝ, ComplexEuclidean dimension))
    (continuousValue : ContinuousOn value (Icc lower 1))
    (differentiates : ∀ radius ∈ Ioo lower 1, HasDerivAt value (derivative radius) radius)
    (radius : Icc lower 1) :
    weightedRadialSection dimension lower positive bounded
      (continuousRadialRealization dimension lower positive bounded (value lower) derivative) radius = value radius.val := by
  rw [continuousRadialRealization_section]
  have fundamental := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le radius.property.1
    (continuousValue.mono (Icc_subset_Icc le_rfl radius.property.2))
    (fun point member => differentiates point ⟨member.1, member.2.trans_le radius.property.2⟩)
    (derivative.continuous.intervalIntegrable lower radius.val)
  rw [fundamental]
  abel

end Grad.AnnularLowCompletion
