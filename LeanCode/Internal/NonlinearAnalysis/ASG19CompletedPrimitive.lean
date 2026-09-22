import ASG18PrimitiveEnergyBound

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem completedPrimitive_exists (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) :
    ∃ primitive : CollarL2 (ComplexEuclidean dimension) lower →L[ℝ] WeightedRadialH1 dimension lower,
      (∀ core, primitive (smoothRadialValueL2 dimension lower core) = anchoredPrimitiveInto dimension lower core) ∧
      (∀ derivative, ‖primitive derivative‖ ≤ Real.sqrt 5 * ‖derivative‖) := by
  have nonnegative : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have estimate := anchoredPrimitiveInto_bound dimension lower positive bounded
  have result : ∃ extension : (LinearMap.range (smoothRadialValueL2 dimension lower)).topologicalClosure →L[ℝ]
      WeightedRadialH1 dimension lower,
      (∀ core, extension ⟨smoothRadialValueL2 dimension lower core,
        Submodule.le_topologicalClosure _ ⟨core, rfl⟩⟩ = anchoredPrimitiveInto dimension lower core) ∧
      (∀ field, ‖extension field‖ ≤ Real.sqrt 5 * ‖field‖) := by
    with_reducible exact (collarRange_extension
      (C := SmoothRadialCore dimension) (F := CollarL2 (ComplexEuclidean dimension) lower)
      (T := WeightedRadialH1 dimension lower)
      (smoothRadialValueL2 dimension lower) (anchoredPrimitiveInto dimension lower)
      (Real.sqrt 5) nonnegative estimate)
  obtain ⟨extension, coreLaw, bound⟩ := result
  let inclusion : CollarL2 (ComplexEuclidean dimension) lower →L[ℝ]
      (LinearMap.range (smoothRadialValueL2 dimension lower)).topologicalClosure :=
    (ContinuousLinearMap.id ℝ _).codRestrict _ (fun field => smoothRadialValueL2_denseRange dimension lower field)
  refine ⟨extension.comp inclusion, ?_, ?_⟩
  · intro core
    exact coreLaw core
  · intro derivative
    exact bound (inclusion derivative)

def completedPrimitive (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) :
    CollarL2 (ComplexEuclidean dimension) lower →L[ℝ] WeightedRadialH1 dimension lower :=
  (completedPrimitive_exists dimension lower positive bounded).choose

theorem completedPrimitive_core (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (core : SmoothRadialCore dimension) :
    completedPrimitive dimension lower positive bounded (smoothRadialValueL2 dimension lower core) =
      anchoredPrimitiveInto dimension lower core :=
  (completedPrimitive_exists dimension lower positive bounded).choose_spec.1 core

theorem completedPrimitive_slope (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (derivative : CollarL2 (ComplexEuclidean dimension) lower) :
    weightedRadialCoordinate dimension lower 1 (completedPrimitive dimension lower positive bounded derivative) =
      radialSqrtMap dimension lower derivative := by
  apply isClosed_property (smoothRadialValueL2_denseRange dimension lower)
    (isClosed_eq ((weightedRadialCoordinate dimension lower 1).continuous.comp
      (completedPrimitive dimension lower positive bounded).continuous)
      (radialSqrtMap dimension lower).continuous) _ derivative
  intro core
  simp only [Function.comp_apply]
  rw [completedPrimitive_core]
  change weightedCurveLinear dimension lower (anchoredPrimitiveCore dimension lower core).val.val.2 = _
  rw [anchoredPrimitiveCore_slope]
  exact (radialSqrtMap_core dimension lower core.val.val.1).symm

theorem completedPrimitive_ordinary_slope (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (derivative : CollarL2 (ComplexEuclidean dimension) lower) :
    collarH1Coordinate (ComplexEuclidean dimension) lower 1
      (weightedToOrdinary dimension lower positive bounded.le
        (completedPrimitive dimension lower positive bounded derivative)) = derivative := by
  apply radialSqrtMap_injective dimension lower positive
  rw [← weightedRadialCoordinate_eq_sqrt dimension lower positive bounded.le,
    completedPrimitive_slope]

theorem completedPrimitive_lower (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (derivative : CollarL2 (ComplexEuclidean dimension) lower) :
    weightedRadialTrace dimension lower positive bounded 0
      (completedPrimitive dimension lower positive bounded derivative) = 0 := by
  apply isClosed_property (smoothRadialValueL2_denseRange dimension lower)
    (isClosed_eq ((weightedRadialTrace dimension lower positive bounded 0).continuous.comp
      (completedPrimitive dimension lower positive bounded).continuous) continuous_const) _ derivative
  intro core
  simp only [Function.comp_apply]
  rw [completedPrimitive_core]
  change weightedRadialTrace dimension lower positive bounded 0
    (weightedRadialCoreInto dimension lower (anchoredPrimitiveCore dimension lower core)) = _
  rw [weightedRadialTrace_core]
  exact anchoredPrimitiveCore_lower dimension lower core

end Grad.AnnularSourceGraph
