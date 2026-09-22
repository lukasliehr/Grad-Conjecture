import AKBY4SameNativeAllMomentData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.CartesianState Grad.SpatialDilation

theorem startupWeighted_sameField {dimension : ℕ} (parameters : PhaseParameters)
    (raw : ℤ → Spatial → PhysicalValue dimension) (first second : StartupL2 dimension)
    (one : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      first point cell = cartesianWeight parameters cell point • raw cell point)
    (two : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      second point cell = cartesianWeight parameters cell point • raw cell point) : first = second := by
  apply Lp.ext
  filter_upwards [one,two] with point firstAt secondAt
  apply lp.ext
  funext cell
  exact (firstAt cell).trans (secondAt cell).symm

variable {parameters : PhaseParameters} {covariantRaw : ℤ → Spatial → PhysicalValue 3}
  {xiOverRadiusRaw : ℤ → Spatial → PhysicalValue 1}
  (data : OriginalNativeAllMoments parameters covariantRaw xiOverRadiusRaw)

/-- Anchor every moment to any already accepted SAME native base field. -/
def OriginalNativeAllMoments.onExisting
    (existing : OriginalNativeMoments parameters covariantRaw xiOverRadiusRaw) :
    OriginalNativeAllMoments parameters covariantRaw xiOverRadiusRaw where
  covariant := data.covariant.withField existing.covariant.field
    (startupWeighted_sameField parameters covariantRaw _ _ data.covariant_same existing.covariant_same)
  xiOverRadius := data.xiOverRadius.withField existing.xiOverRadius.field
    (startupWeighted_sameField parameters xiOverRadiusRaw _ _ data.xiOverRadius_same existing.xiOverRadius_same)
  covariant_same := existing.covariant_same
  xiOverRadius_same := existing.xiOverRadius_same

def OriginalNativeAllMoments.scaledCovariant (scale : Scale) : StartupAllMoments 3 := data.covariant.dilate scale

def OriginalNativeAllMoments.scaledXiOverRadius (scale : Scale) : StartupAllMoments 1 := data.xiOverRadius.dilate scale

def OriginalNativeAllMoments.scaledPsi (scale : Scale) : StartupAllMoments 1 := (data.scaledXiOverRadius scale).radiusMultiply

theorem OriginalNativeAllMoments.scaledCovariant_same (scale : Scale) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (data.scaledCovariant scale).field point cell =
        Grad.AnalyticWeights.Calculus.physicalWeight parameters.sigma0 parameters.gamma scale.val cell point •
          covariantRaw cell (scale.val • point) :=
  startupMomentDilation_weighted_same parameters.sigma0 parameters.gamma scale covariantRaw data.covariant.field data.covariant_same

theorem OriginalNativeAllMoments.scaledXiOverRadius_same (scale : Scale) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (data.scaledXiOverRadius scale).field point cell =
        Grad.AnalyticWeights.Calculus.physicalWeight parameters.sigma0 parameters.gamma scale.val cell point •
          xiOverRadiusRaw cell (scale.val • point) :=
  startupMomentDilation_weighted_same parameters.sigma0 parameters.gamma scale xiOverRadiusRaw data.xiOverRadius.field data.xiOverRadius_same

theorem OriginalNativeAllMoments.scaledPsi_same (scale : Scale) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (data.scaledPsi scale).field point cell =
        Grad.AnalyticWeights.Calculus.physicalWeight parameters.sigma0 parameters.gamma scale.val cell point •
          (‖point‖ • xiOverRadiusRaw cell (scale.val • point)) :=
  startupRadiusMultiply_dilation_weighted parameters.sigma0 parameters.gamma scale xiOverRadiusRaw data.xiOverRadius.field data.xiOverRadius_same

theorem OriginalNativeAllMoments.scaledPsi_originalXi (scale : Scale) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (data.scaledPsi scale).field point cell =
        Grad.AnalyticWeights.Calculus.physicalWeight parameters.sigma0 parameters.gamma scale.val cell point •
          (scale.val⁻¹ • (‖scale.val • point‖ • xiOverRadiusRaw cell (scale.val • point))) := by
  filter_upwards [data.scaledPsi_same scale] with point same
  intro cell
  rw [scaledXi_fromRadius]
  exact same cell

theorem OriginalNativeAllMoments.onExisting_scaledCovariant
    (existing : OriginalNativeMoments parameters covariantRaw xiOverRadiusRaw) (scale : Scale) :
    ((data.onExisting existing).scaledCovariant scale).field = (existing.scaledCovariant scale).field := rfl

theorem OriginalNativeAllMoments.onExisting_scaledXiOverRadius
    (existing : OriginalNativeMoments parameters covariantRaw xiOverRadiusRaw) (scale : Scale) :
    ((data.onExisting existing).scaledXiOverRadius scale).field = (existing.scaledXiOverRadius scale).field := rfl

theorem OriginalNativeAllMoments.onExisting_scaledPsi
    (existing : OriginalNativeMoments parameters covariantRaw xiOverRadiusRaw) (scale : Scale) :
    ((data.onExisting existing).scaledPsi scale).field = (existing.scaledPsi scale).field := rfl

end Grad.CartesianStartup
