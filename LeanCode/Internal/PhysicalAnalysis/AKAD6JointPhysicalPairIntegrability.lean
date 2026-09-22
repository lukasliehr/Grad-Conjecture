import AKAD5ActualBoundedFluxClassicalConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology

namespace Grad.PhysicalAxisEquation
open Grad.PDEBootstrap

/-- The original vector and scalar fields may be assembled into one joint
input for the actual normalized coefficient rows, with no new radial loss. -/
theorem jointPhysicalPair_integrable {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (domain : Set Spatial) (first : Spatial → E) (second : Spatial → F)
    (firstIntegrable : IntegrableOn first domain) (secondIntegrable : IntegrableOn second domain)
    (firstWeighted : IntegrableOn (fun point => ‖point‖⁻¹ * ‖first point‖) domain)
    (secondWeighted : IntegrableOn (fun point => ‖point‖⁻¹ * ‖second point‖) domain) :
    IntegrableOn (fun point => (first point,second point)) domain ∧
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖(first point,second point)‖) domain := by
  have measurable := firstIntegrable.aestronglyMeasurable.prodMk secondIntegrable.aestronglyMeasurable
  have normBound (point : Spatial) : ‖(first point,second point)‖ ≤ ‖first point‖ + ‖second point‖ := by
    rw [Prod.norm_def]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  constructor
  · exact (firstIntegrable.norm.add secondIntegrable.norm).mono' measurable (Eventually.of_forall normBound)
  · apply (firstWeighted.add secondWeighted).mono'
      (measurable_id.norm.inv.aestronglyMeasurable.mul measurable.norm)
    filter_upwards [] with point
    change ‖‖point‖⁻¹ * ‖(first point,second point)‖‖ ≤ ‖point‖⁻¹ * ‖first point‖ + ‖point‖⁻¹ * ‖second point‖
    rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _)),← mul_add]
    exact mul_le_mul_of_nonneg_left (normBound point) (inv_nonneg.mpr (norm_nonneg _))

end Grad.PhysicalAxisEquation
