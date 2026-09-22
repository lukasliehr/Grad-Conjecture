import ASG32UniformRadialRepresentative

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem weightedRadialSection_exists (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) :
    ∃ sectionMap : WeightedRadialH1 dimension lower →L[ℝ] RadialContinuousSection dimension lower,
      (∀ core, sectionMap (weightedRadialCoreInto dimension lower core) = smoothRadialSection dimension lower core) ∧
      (∀ field, ‖sectionMap field‖ ≤ sourceEndpointConstant lower * ‖field‖) := by
  have nonnegative : 0 ≤ sourceEndpointConstant lower := Real.sqrt_nonneg _
  have estimate := smoothRadialSection_bound dimension lower positive bounded
  have result : ∃ extension : (LinearMap.range (weightedRadialCore dimension lower)).topologicalClosure →L[ℝ]
      RadialContinuousSection dimension lower,
      (∀ core, extension ⟨weightedRadialCore dimension lower core,
        Submodule.le_topologicalClosure _ ⟨core, rfl⟩⟩ = smoothRadialSection dimension lower core) ∧
      (∀ field, ‖extension field‖ ≤ sourceEndpointConstant lower * ‖field‖) := by
    with_reducible exact (collarRange_extension
      (C := SmoothRadialCore dimension) (F := WeightedRadialAmbient dimension lower)
      (T := RadialContinuousSection dimension lower)
      (weightedRadialCore dimension lower) (smoothRadialSection dimension lower)
      (sourceEndpointConstant lower) nonnegative estimate)
  obtain ⟨extension, coreLaw, bound⟩ := result
  exact ⟨extension, coreLaw, bound⟩

/-- The actual continuous representative on the closed collar, obtained
as the uniform limit of the same smooth radial graph core. -/
def weightedRadialSection (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) :
    WeightedRadialH1 dimension lower →L[ℝ] RadialContinuousSection dimension lower :=
  (weightedRadialSection_exists dimension lower positive bounded).choose

theorem weightedRadialSection_core (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (core : SmoothRadialCore dimension) :
    weightedRadialSection dimension lower positive bounded (weightedRadialCoreInto dimension lower core) =
      smoothRadialSection dimension lower core :=
  (weightedRadialSection_exists dimension lower positive bounded).choose_spec.1 core

theorem radialEndpointRadius_mem (lower : ℝ) (bounded : lower ≤ 1) (endpoint : Fin 2) :
    radialEndpointRadius lower endpoint ∈ Icc lower 1 := by
  fin_cases endpoint
  · exact ⟨le_rfl, bounded⟩
  · exact ⟨bounded, le_rfl⟩

/-- Both one-sided endpoint values are evaluations of that same continuous
representative; they are not independent completed data. -/
theorem weightedRadialSection_endpoint (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (endpoint : Fin 2)
    (field : WeightedRadialH1 dimension lower) :
    weightedRadialSection dimension lower positive bounded field
      ⟨radialEndpointRadius lower endpoint, radialEndpointRadius_mem lower bounded.le endpoint⟩ =
      weightedRadialTrace dimension lower positive bounded endpoint field := by
  apply isClosed_property (weightedRadialCoreInto_denseRange dimension lower)
    (isClosed_eq ((ContinuousMap.evalCLM ℝ
      ⟨radialEndpointRadius lower endpoint, radialEndpointRadius_mem lower bounded.le endpoint⟩).continuous.comp
        (weightedRadialSection dimension lower positive bounded).continuous)
      (weightedRadialTrace dimension lower positive bounded endpoint).continuous) _ field
  intro core
  simp only [Function.comp_apply]
  rw [weightedRadialSection_core, weightedRadialTrace_core]
  rfl

end Grad.AnnularSourceGraph
