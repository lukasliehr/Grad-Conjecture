import AKAD3OriginalClassicalEnergyAxisConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology

namespace Grad.PhysicalAxisEquation
open Grad.PDEBootstrap

/-- Bounded actual coefficient multipliers preserve exactly the two flux
integrability bounds used at the axis. No derivative of the field enters. -/
theorem boundedPhysicalFlux_integrable_pair {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (domain : Set Spatial) (field : Spatial → E)
    (fieldIntegrable : IntegrableOn field domain)
    (weightedIntegrable : IntegrableOn (fun point => ‖point‖⁻¹ * ‖field point‖) domain)
    (coefficient : Spatial → E →L[ℝ] F)
    (measurable : AEStronglyMeasurable coefficient (volume.restrict domain))
    (C : ℝ) (bounded : ∀ᵐ point ∂volume.restrict domain, ‖coefficient point‖ ≤ C) :
    IntegrableOn (fun point => coefficient point (field point)) domain ∧
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖coefficient point (field point)‖) domain := by
  have evaluation : Continuous (fun item : (E →L[ℝ] F) × E => item.1 item.2) :=
    continuous_fst.clm_apply continuous_snd
  have outputMeasurable := evaluation.comp_aestronglyMeasurable
    (measurable.prodMk fieldIntegrable.aestronglyMeasurable)
  have bound : ∀ᵐ point ∂volume.restrict domain, ‖coefficient point (field point)‖ ≤ C * ‖field point‖ := by
    filter_upwards [bounded] with point bound
    exact ((coefficient point).le_opNorm (field point)).trans
      (mul_le_mul_of_nonneg_right bound (norm_nonneg _))
  constructor
  · exact (fieldIntegrable.norm.const_mul C).mono' outputMeasurable bound
  · apply (weightedIntegrable.const_mul C).mono'
      (measurable_id.norm.inv.aestronglyMeasurable.mul outputMeasurable.norm)
    filter_upwards [bound] with point bound
    change ‖‖point‖⁻¹ * ‖coefficient point (field point)‖‖ ≤ C * (‖point‖⁻¹ * ‖field point‖)
    rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))]
    exact (mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr (norm_nonneg point))).trans_eq (by ring)

end Grad.PhysicalAxisEquation
