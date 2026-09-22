import ASG36ExactRadialPrimitive

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem radialSectionL2_ae (dimension : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (sectionValue : RadialContinuousSection dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      radialSectionExtension dimension lower bounded sectionValue radius =
        radialSectionL2 dimension lower positive bounded sectionValue radius := by
  exact ((collarContinuous_memLp (ComplexEuclidean dimension) lower
    (radialSectionExtension dimension lower bounded sectionValue)).coeFn_toLp).symm

theorem weightedRadialSection_ae (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : WeightedRadialH1 dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      radialSectionExtension dimension lower bounded.le
        (weightedRadialSection dimension lower positive bounded field) radius =
      collarH1Coordinate (ComplexEuclidean dimension) lower 0
        (weightedToOrdinary dimension lower positive bounded.le field) radius := by
  rw [← weightedRadialSection_bulk dimension lower positive bounded field]
  exact radialSectionL2_ae dimension lower positive bounded.le _

/-- Both endpoint traces satisfy the actual fundamental theorem on the
same representative, with the genuine weak radial derivative. -/
theorem weightedRadialTrace_fundamental (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : WeightedRadialH1 dimension lower) :
    weightedRadialTrace dimension lower positive bounded 1 field =
      weightedRadialTrace dimension lower positive bounded 0 field +
        ∫ point in lower..1, collarH1Coordinate (ComplexEuclidean dimension) lower 1
          (weightedToOrdinary dimension lower positive bounded.le field) point := by
  have primitive := weightedRadialSection_primitive dimension lower positive bounded field
    ⟨1, bounded.le, le_rfl⟩
  have endpoint := weightedRadialSection_endpoint dimension lower positive bounded 1 field
  exact endpoint.symm.trans primitive

/-- AG2/V4 consumer for actual annular ODE recovery: every original compact
weak L2 pair has a continuous representative on the closed collar, equal a.e.
to the original bulk and literally its anchored Bochner primitive. -/
theorem actualCompactWeakRadialRepresentative (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (value derivative : CollarL2 (ComplexEuclidean dimension) lower)
    (weak : CompactWeakDerivative dimension lower value derivative) :
    ∃ representative : RadialContinuousSection dimension lower,
      (∀ᵐ radius ∂volume.restrict (Icc lower 1),
        radialSectionExtension dimension lower bounded.le representative radius = value radius) ∧
      ∀ radius : Icc lower (1 : ℝ),
        representative radius = representative ⟨lower, le_rfl, bounded.le⟩ +
          ∫ point in lower..radius.val, derivative point := by
  obtain ⟨field, valueLaw, slopeLaw⟩ := compactWeakPair_in_weightedCompletion dimension lower positive bounded value derivative weak
  refine ⟨weightedRadialSection dimension lower positive bounded field, ?_, ?_⟩
  · have actual := weightedRadialSection_ae dimension lower positive bounded field
    rwa [valueLaw] at actual
  · intro radius
    have primitive := weightedRadialSection_primitive dimension lower positive bounded field radius
    rw [slopeLaw] at primitive
    have endpoint := weightedRadialSection_endpoint dimension lower positive bounded 0 field
    exact primitive.trans (congrArg (fun base => base + ∫ point in lower..radius.val, derivative point) endpoint.symm)

end Grad.AnnularSourceGraph
