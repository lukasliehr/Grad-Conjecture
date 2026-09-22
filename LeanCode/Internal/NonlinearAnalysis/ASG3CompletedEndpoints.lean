import ASG2BothEndpointBounds

noncomputable section

set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem weightedRadialTrace_exists (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (endpoint : Fin 2) :
    ∃ trace : WeightedRadialH1 dimension lower →L[ℝ] ComplexEuclidean dimension,
      (∀ core, trace (weightedRadialCoreInto dimension lower core) =
        core.val.val.1 (radialEndpointRadius lower endpoint)) ∧
      (∀ field, ‖trace field‖ ≤ sourceEndpointConstant lower * ‖field‖) :=
by
  have nonnegative : 0 ≤ sourceEndpointConstant lower := Real.sqrt_nonneg _
  have estimate := smoothRadialEndpoint_bound dimension lower positive bounded endpoint
  have extension : ∃ trace : (LinearMap.range (weightedRadialCore dimension lower)).topologicalClosure →L[ℝ] ComplexEuclidean dimension,
      (∀ core, trace ⟨weightedRadialCore dimension lower core,
        Submodule.le_topologicalClosure _ ⟨core, rfl⟩⟩ = smoothRadialEndpoint dimension lower endpoint core) ∧
      (∀ field, ‖trace field‖ ≤ sourceEndpointConstant lower * ‖field‖) := by
    with_reducible exact (collarRange_extension
      (C := SmoothRadialCore dimension) (F := WeightedRadialAmbient dimension lower)
      (T := ComplexEuclidean dimension) (weightedRadialCore dimension lower)
      (smoothRadialEndpoint dimension lower endpoint) (sourceEndpointConstant lower)
      nonnegative estimate)
  obtain ⟨trace, coreLaw, bound⟩ := extension
  refine ⟨trace, ?_, bound⟩
  intro core
  exact coreLaw core

/-- Both completed endpoints are forced by the same smooth radial graph.
There is no independent endpoint value in the completed source carrier. -/
def weightedRadialTrace (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (endpoint : Fin 2) :
    WeightedRadialH1 dimension lower →L[ℝ] ComplexEuclidean dimension :=
  (weightedRadialTrace_exists dimension lower positive bounded endpoint).choose

theorem weightedRadialTrace_core (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (endpoint : Fin 2) (core : SmoothRadialCore dimension) :
    weightedRadialTrace dimension lower positive bounded endpoint (weightedRadialCoreInto dimension lower core) =
      core.val.val.1 (radialEndpointRadius lower endpoint) :=
  (weightedRadialTrace_exists dimension lower positive bounded endpoint).choose_spec.1 core

theorem weightedRadialTrace_bound (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (endpoint : Fin 2) (field : WeightedRadialH1 dimension lower) :
    ‖weightedRadialTrace dimension lower positive bounded endpoint field‖ ≤
      sourceEndpointConstant lower * ‖field‖ :=
  (weightedRadialTrace_exists dimension lower positive bounded endpoint).choose_spec.2 field

theorem weightedRadialTrace_unique (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (endpoint : Fin 2)
    (trace : WeightedRadialH1 dimension lower →L[ℝ] ComplexEuclidean dimension)
    (coreLaw : ∀ core, trace (weightedRadialCoreInto dimension lower core) =
      core.val.val.1 (radialEndpointRadius lower endpoint)) :
    trace = weightedRadialTrace dimension lower positive bounded endpoint := by
  apply ContinuousLinearMap.ext
  intro field
  apply isClosed_property (weightedRadialCoreInto_denseRange dimension lower)
    (isClosed_eq trace.continuous (weightedRadialTrace dimension lower positive bounded endpoint).continuous) _ field
  intro core
  rw [coreLaw, weightedRadialTrace_core]

/-- The outer endpoint agrees with the already accepted literal weighted
radial endpoint relation on every completed source. -/
theorem weightedRadialTrace_outer_relation (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : WeightedRadialH1 dimension lower) :
    ((weightedRadialCoordinate dimension lower 0 field, weightedRadialCoordinate dimension lower 1 field),
      weightedRadialTrace dimension lower positive bounded 1 field) ∈ radialEndpointGraph dimension lower := by
  have closed : IsClosed {point : WeightedRadialH1 dimension lower |
      ((weightedRadialCoordinate dimension lower 0 point, weightedRadialCoordinate dimension lower 1 point),
        weightedRadialTrace dimension lower positive bounded 1 point) ∈ radialEndpointGraph dimension lower} :=
    (LinearMap.range (weightedEndpointCore dimension lower)).isClosed_topologicalClosure.preimage
      (((weightedRadialCoordinate dimension lower 0).continuous.prodMk
        (weightedRadialCoordinate dimension lower 1).continuous).prodMk
        (weightedRadialTrace dimension lower positive bounded 1).continuous)
  apply isClosed_property (weightedRadialCoreInto_denseRange dimension lower) closed _ field
  intro core
  rw [weightedRadialCoordinate_core_zero, weightedRadialCoordinate_core_one, weightedRadialTrace_core]
  exact radialEndpointGraph_core dimension lower core.val

end Grad.AnnularSourceGraph
