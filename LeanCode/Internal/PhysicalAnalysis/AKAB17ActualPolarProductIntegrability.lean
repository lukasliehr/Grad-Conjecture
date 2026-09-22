import AKAB16AngularL1FromActualCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Grad.WeightedAxisRemoval
open Grad.ClosedJets Grad.SourceCollarCoefficients Grad.BoundaryTrace

/-- Exact angular coefficients of an integrable physical Hilbert curve
control the actual two-variable field, including every angular mode. -/
theorem actualPolarField_integrable {dimension : ℕ}
    (curve : ℝ → CellL2 dimension) (cell : ℤ)
    (field : ℝ × ℝ → ComplexEuclidean dimension)
    (curveIntegrable : IntegrableOn curve (Ioc (0 : ℝ) 1))
    (measurable : AEStronglyMeasurable field
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (-Real.pi) Real.pi))))
    (continuousSlices : ∀ᵐ radius ∂volume.restrict (Ioc (0 : ℝ) 1),
      Continuous (fun angle => field (radius,angle)))
    (same : ∀ᵐ radius ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ mode,
      angularCoefficient (fun angle => field (radius,angle)) mode = curve radius (mode,cell)) :
    IntegrableOn field (Ioc (0 : ℝ) 1 ×ˢ Ioc (-Real.pi) Real.pi) := by
  have product : Integrable field
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (-Real.pi) Real.pi))) := by
    apply (integrable_prod_iff measurable).mpr
    constructor
    · filter_upwards [continuousSlices] with radius continuousSlice
      exact continuousSlice.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · apply (curveIntegrable.norm.const_mul (2 * Real.pi)).mono'
        measurable.norm.integral_prod_right'
      filter_upwards [continuousSlices,same] with radius continuousSlice coefficient
      rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      exact angularPhysicalField_integral_norm_bound (curve radius) cell _ continuousSlice coefficient
  simpa only [IntegrableOn,Measure.prod_restrict,← Measure.volume_eq_prod] using product

end Grad.WeightedAxisRemoval
