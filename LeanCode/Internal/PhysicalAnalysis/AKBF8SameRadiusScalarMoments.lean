import AKBF7SameDimensionDilation
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.SpatialDilation

theorem startupRadius_memLp : MemLp (fun point : Spatial => ‖point‖) ⊤ (volume.restrict openUnitDisk) := by
  apply memLp_top_of_bound (continuous_norm.aestronglyMeasurable) 1
  filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point inside
  simpa only [norm_norm] using inside.le

/-- Multiplication by the actual radius on the unit disk. -/
def startupRadiusMultiply {dimension : ℕ} (field : StartupL2 dimension) : StartupL2 dimension :=
  ((Lp.memLp field).smul startupRadius_memLp).toLp (fun point => ‖point‖ • field point)

theorem startupRadiusMultiply_ae {dimension : ℕ} (field : StartupL2 dimension) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, startupRadiusMultiply field point = ‖point‖ • field point :=
  MemLp.coeFn_toLp _

theorem startupRadiusMultiply_norm {dimension : ℕ} (field : StartupL2 dimension) :
    ‖startupRadiusMultiply field‖ ≤ ‖field‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [startupRadiusMultiply_ae field,ae_restrict_mem openUnitDisk_isOpen.measurableSet]
    with point same inside
  rw [same,norm_smul,Real.norm_of_nonneg (norm_nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg _) inside.le

def StartupMoments.radiusMultiply {dimension : ℕ} (family : StartupMoments dimension) : StartupMoments dimension where
  field := startupRadiusMultiply family.field
  moment grade := startupRadiusMultiply (family.moment grade)
  zero := congrArg startupRadiusMultiply family.zero
  same := by
    apply ae_all_iff.mpr
    intro grade
    filter_upwards [startupRadiusMultiply_ae family.field,startupRadiusMultiply_ae (family.moment grade),family.same]
      with point fieldAt momentAt same
    intro cell
    rw [momentAt,fieldAt]
    simp only [lp.coeFn_smul,Pi.smul_apply]
    rw [same grade cell]
    exact smul_comm _ _ _

/-- The scalar startup field is radius times the SAME dilated Xi/r. -/
theorem startupRadiusMultiply_dilation_weighted {dimension : ℕ} (sigma gamma : ℝ) (scale : Scale)
    (raw : ℤ → Spatial → PhysicalValue dimension) (field : StartupL2 dimension)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      field point cell = Grad.AnalyticWeights.Calculus.physicalWeight sigma gamma 1 cell point • raw cell point) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      startupRadiusMultiply (startupMomentDilation scale field) point cell =
        Grad.AnalyticWeights.Calculus.physicalWeight sigma gamma scale.val cell point •
          (‖point‖ • raw cell (scale.val • point)) := by
  filter_upwards [startupRadiusMultiply_ae (startupMomentDilation scale field),
    startupMomentDilation_weighted_same sigma gamma scale raw field same] with point multiplied weighted
  intro cell
  rw [multiplied]
  simp only [lp.coeFn_smul,Pi.smul_apply]
  rw [weighted cell]
  exact smul_comm _ _ _

/-- Exact psi(Y)=Xi(ell Y)/ell, including the unchanged positive ell. -/
theorem scaledXi_fromRadius {dimension : ℕ} (scale : Scale) (raw : Spatial → PhysicalValue dimension) (point : Spatial) :
    scale.val⁻¹ • (‖scale.val • point‖ • raw (scale.val • point)) = ‖point‖ • raw (scale.val • point) := by
  rw [norm_smul,Real.norm_of_nonneg scale.property.1.le,smul_smul,← mul_assoc,inv_mul_cancel₀ scale.property.1.ne',one_mul]

end Grad.CartesianStartup
