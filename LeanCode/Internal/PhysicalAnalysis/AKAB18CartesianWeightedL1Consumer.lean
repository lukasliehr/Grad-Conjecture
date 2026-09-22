import AKAB15ExactPolarDiskMeasure
import AKAB17ActualPolarProductIntegrability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Grad.WeightedAxisRemoval
open Grad.ClosedJets Grad.DiskExtension.Operator

/-- Integrability with respect to dr dθ controls both the Cartesian field
and its radial inverse norm. The Jacobian cancels exactly in the second bound. -/
theorem cartesian_integrable_pair_of_polar {E : Type*} [NormedAddCommGroup E]
    (field : SpatialPlane → E)
    (measurable : AEStronglyMeasurable field (volume.restrict openUnitDisk))
    (polar : IntegrableOn (fun point : ℝ × ℝ => field (spatialPlaneOfPair (polarCoord.symm point)))
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi)) :
    IntegrableOn field openUnitDisk ∧
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖field point‖) openUnitDisk := by
  constructor
  · apply openDisk_integrable_of_polar field measurable
    apply polar.norm.mono'
      (measurable_fst.aestronglyMeasurable.mul polar.aestronglyMeasurable.norm)
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with point inside
    change ‖point.1 * ‖field (spatialPlaneOfPair (polarCoord.symm point))‖‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg inside.1.1.le (norm_nonneg _))]
    exact mul_le_of_le_one_left (norm_nonneg _) inside.1.2.le
  · apply openDisk_integrable_of_polar (fun point => ‖point‖⁻¹ * ‖field point‖)
      (measurable_id.norm.inv.aestronglyMeasurable.mul measurable.norm)
    apply polar.norm.congr
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with point inside
    rw [spatialPlaneOfPair_polar_norm point.1 point.2 inside.1.1.le,
      Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr inside.1.1.le) (norm_nonneg _)),
      ← mul_assoc,mul_inv_cancel₀ inside.1.1.ne',one_mul]

end Grad.WeightedAxisRemoval
