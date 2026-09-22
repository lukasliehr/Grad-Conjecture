import ASG35ActualIntervalIntegral

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem radialIntervalIntegral_core (dimension : ℕ) (lower : ℝ) (radius : Icc lower (1 : ℝ))
    (curve : C(ℝ, ComplexEuclidean dimension)) :
    radialIntervalIntegral dimension lower radius (collarContinuousL2 (ComplexEuclidean dimension) lower curve) =
      ∫ point in lower..radius.val, curve point := by
  rw [radialIntervalIntegral_apply, intervalIntegral.integral_of_le radius.property.1,
    intervalIntegral.integral_of_le radius.property.1, ← integral_Icc_eq_integral_Ioc,
    ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  have representative := (collarContinuous_memLp (ComplexEuclidean dimension) lower curve).coeFn_toLp
  exact ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc le_rfl radius.property.2) representative

/-- AG2's actual integral representative, including both one-sided endpoints.
The derivative is the same L2 coordinate of the completed radial graph. -/
theorem weightedRadialSection_primitive (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : WeightedRadialH1 dimension lower)
    (radius : Icc lower (1 : ℝ)) :
    weightedRadialSection dimension lower positive bounded field radius =
      weightedRadialTrace dimension lower positive bounded 0 field +
        ∫ point in lower..radius.val,
          collarH1Coordinate (ComplexEuclidean dimension) lower 1
            (weightedToOrdinary dimension lower positive bounded.le field) point := by
  rw [← radialIntervalIntegral_apply dimension lower radius]
  apply isClosed_property (weightedRadialCoreInto_denseRange dimension lower)
    (isClosed_eq ((ContinuousMap.evalCLM ℝ radius).continuous.comp
      (weightedRadialSection dimension lower positive bounded).continuous)
      ((weightedRadialTrace dimension lower positive bounded 0).continuous.add
        ((radialIntervalIntegral dimension lower radius).continuous.comp
          ((collarH1Coordinate (ComplexEuclidean dimension) lower 1).continuous.comp
            (weightedToOrdinary dimension lower positive bounded.le).continuous)))) _ field
  intro core
  simp only [Pi.add_apply, Function.comp_apply]
  rw [weightedRadialSection_core, weightedRadialTrace_core, weightedToOrdinary_core,
    collarH1Coordinate_core_one, radialIntervalIntegral_core]
  change core.val.val.1 radius.val = core.val.val.1 lower + ∫ point in lower..radius.val, core.val.val.2 point
  have fundamental := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun point _ => core.val.property point)
    (core.val.val.2.continuous.intervalIntegrable lower radius.val)
  rw [fundamental]
  abel

/-- In particular the completed anchored primitive is literally ∫_a^r g,
with g arbitrary L2 and no strong representative premise. -/
theorem completedPrimitive_section (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (derivative : CollarL2 (ComplexEuclidean dimension) lower)
    (radius : Icc lower (1 : ℝ)) :
    weightedRadialSection dimension lower positive bounded
      (completedPrimitive dimension lower positive bounded derivative) radius =
        ∫ point in lower..radius.val, derivative point := by
  rw [weightedRadialSection_primitive, completedPrimitive_lower, zero_add,
    completedPrimitive_ordinary_slope]

end Grad.AnnularSourceGraph
