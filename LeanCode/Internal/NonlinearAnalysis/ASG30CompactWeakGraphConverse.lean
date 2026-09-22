import ASG29CompactWeakConstants

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The anchored primitive plus a genuine constant realizes every L2 weak
pair in the original C∞ weighted graph closure. -/
theorem compactWeakPair_in_weightedCompletion (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (value derivative : CollarL2 (ComplexEuclidean dimension) lower)
    (weak : CompactWeakDerivative dimension lower value derivative) :
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
  have primitiveCompact := collarWeak_isCompact dimension lower _ derivative primitiveWeak
  have differenceWeak : CompactWeakDerivative dimension lower
      (value - collarH1Coordinate (ComplexEuclidean dimension) lower 0 ordinary) 0 := by
    intro test smooth compact supported vector
    have same := neg_injective ((weak test smooth compact supported vector).symm.trans
      (primitiveCompact test smooth compact supported vector))
    rw [map_zero, map_sub, same, sub_self, neg_zero]
  obtain ⟨constant, constantLaw⟩ := compactWeakZero_eq_constant dimension lower bounded _ differenceWeak
  refine ⟨primitive + weightedRadialCoreInto dimension lower (constantRadialCore dimension constant), ?_, ?_⟩
  · rw [map_add, map_add, weightedToOrdinary_core, collarH1Coordinate_core_zero]
    change collarH1Coordinate (ComplexEuclidean dimension) lower 0 ordinary +
      constantRadialL2 dimension lower constant = value
    exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp constantLaw).symm
  · rw [map_add, map_add, weightedToOrdinary_core, collarH1Coordinate_core_one, constantRadialCore_slope, map_zero, add_zero]
    exact slope

/-- The paper's compact distributional tests and the accepted full
endpoint-zero C1 test class define exactly the same finite L2 graph. -/
theorem compactWeak_iff_collarWeak (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (value derivative : CollarL2 (ComplexEuclidean dimension) lower) :
    CompactWeakDerivative dimension lower value derivative ↔ CollarWeakDerivative lower value derivative := by
  constructor
  · intro weak
    obtain ⟨field, valueLaw, slopeLaw⟩ := compactWeakPair_in_weightedCompletion dimension lower positive bounded value derivative weak
    have graphWeak := weightedRadial_weak dimension lower positive bounded.le field
    rwa [valueLaw, slopeLaw] at graphWeak
  · exact collarWeak_isCompact dimension lower value derivative

end Grad.AnnularSourceGraph
