import ASG21WeakZeroConstants

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The anchored primitive plus a genuine constant realizes every L2 weak
pair in the original C∞ weighted graph closure. -/
theorem weakPair_in_weightedCompletion (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (value derivative : CollarL2 (ComplexEuclidean dimension) lower)
    (weak : CollarWeakDerivative lower value derivative) :
    ∃ field : WeightedRadialH1 dimension lower,
      collarH1Coordinate (ComplexEuclidean dimension) lower 0
        (weightedToOrdinary dimension lower positive bounded.le field) = value ∧
      collarH1Coordinate (ComplexEuclidean dimension) lower 1
        (weightedToOrdinary dimension lower positive bounded.le field) = derivative := by
  let primitive := completedPrimitive dimension lower positive bounded derivative
  let ordinary := weightedToOrdinary dimension lower positive bounded.le primitive
  have slope : collarH1Coordinate (ComplexEuclidean dimension) lower 1 ordinary = derivative :=
    completedPrimitive_ordinary_slope dimension lower positive bounded derivative
  have primitiveWeak : CollarWeakDerivative lower
      (collarH1Coordinate (ComplexEuclidean dimension) lower 0 ordinary)
      (collarH1Coordinate (ComplexEuclidean dimension) lower 1 ordinary) :=
    collarH1_weak lower bounded.le ordinary
  rw [slope] at primitiveWeak
  have differenceWeak : CollarWeakDerivative lower
      (value - collarH1Coordinate (ComplexEuclidean dimension) lower 0 ordinary) 0 := by
    intro test vector
    have same := neg_injective ((weak test vector).symm.trans (primitiveWeak test vector))
    rw [map_zero, map_sub, same, sub_self, neg_zero]
  obtain ⟨constant, constantLaw⟩ := weakZero_eq_constant dimension lower bounded _ differenceWeak
  refine ⟨primitive + weightedRadialCoreInto dimension lower (constantRadialCore dimension constant), ?_, ?_⟩
  · rw [map_add, map_add, weightedToOrdinary_core, collarH1Coordinate_core_zero]
    change collarH1Coordinate (ComplexEuclidean dimension) lower 0 ordinary +
      constantRadialL2 dimension lower constant = value
    exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp constantLaw).symm
  · rw [map_add, map_add, weightedToOrdinary_core, collarH1Coordinate_core_one, constantRadialCore_slope, map_zero, add_zero]
    exact slope

/-- Equivalent literal r dr coordinates of the reverse construction. -/
theorem weakPair_weighted_coordinates (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (value derivative : CollarL2 (ComplexEuclidean dimension) lower)
    (weak : CollarWeakDerivative lower value derivative) :
    ∃ field : WeightedRadialH1 dimension lower,
      weightedRadialCoordinate dimension lower 0 field = radialSqrtMap dimension lower value ∧
      weightedRadialCoordinate dimension lower 1 field = radialSqrtMap dimension lower derivative := by
  obtain ⟨field, valueLaw, slopeLaw⟩ := weakPair_in_weightedCompletion dimension lower positive bounded value derivative weak
  refine ⟨field, ?_, ?_⟩
  · rw [weightedRadialCoordinate_eq_sqrt dimension lower positive bounded.le, valueLaw]
  · rw [weightedRadialCoordinate_eq_sqrt dimension lower positive bounded.le, slopeLaw]

/-- Exact radial graph characterization. The reverse direction is a theorem,
not an added source-domain assumption. -/
theorem weightedRadialH1_iff_weakPair (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (value derivative : CollarL2 (ComplexEuclidean dimension) lower) :
    CollarWeakDerivative lower value derivative ↔
      ∃ field : WeightedRadialH1 dimension lower,
        collarH1Coordinate (ComplexEuclidean dimension) lower 0
          (weightedToOrdinary dimension lower positive bounded.le field) = value ∧
        collarH1Coordinate (ComplexEuclidean dimension) lower 1
          (weightedToOrdinary dimension lower positive bounded.le field) = derivative := by
  constructor
  · exact weakPair_in_weightedCompletion dimension lower positive bounded value derivative
  · rintro ⟨field, rfl, rfl⟩
    exact weightedRadial_weak dimension lower positive bounded.le field

end Grad.AnnularSourceGraph
