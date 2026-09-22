import AKBN10RawThirdEquationConsumer
import AKBF10ActualSameNativeMomentData
import AKBH7ActualForceCorrectionMoments
import AKBO4ActualOriginalSourceCarriers

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 850000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState Grad.SpatialDilation

/-- The actual native weighted bounds give the SAME unweighted covariant
and Xi, retaining all frequency moments before Cartesian regularity. -/
theorem OriginalNativeMoments.raw_fields (parameters : PhaseParameters)
    (covariantRaw : ℤ → Spatial → PhysicalValue 3) (xiOverRadiusRaw : ℤ → Spatial → PhysicalValue 1)
    (native : OriginalNativeMoments parameters covariantRaw xiOverRadiusRaw) :
    ∃ covariant : StartupMoments 3, ∃ xi : StartupMoments 1,
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, covariant.field point cell = covariantRaw cell point) ∧
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, xi.field point cell = ‖point‖ • xiOverRadiusRaw cell point) := by
  let one : Scale := ⟨1,by constructor <;> norm_num⟩
  let covariant := native.covariant.unweight parameters one
  let xiOverRadius := native.xiOverRadius.unweight parameters one
  have sameCovariant := native.covariant.unweight_same parameters one covariantRaw native.covariant_same
  have sameXi := native.xiOverRadius.unweight_same parameters one xiOverRadiusRaw native.xiOverRadius_same
  refine ⟨covariant,xiOverRadius.radiusMultiply,sameCovariant,?_⟩
  filter_upwards [startupRadiusMultiply_ae xiOverRadius.field,sameXi] with point multiplied actual
  intro cell
  change startupRadiusMultiply xiOverRadius.field point cell = _
  rw [multiplied]
  change ‖point‖ • xiOverRadius.field point cell = _
  rw [actual cell]

end Grad.CartesianStartup
