import AKBF8SameRadiusScalarMoments
import AKBF10ActualSameNativeMomentData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.CartesianState Grad.SpatialDilation

variable {parameters : PhaseParameters} {covariantRaw : ℤ → Spatial → PhysicalValue 3}
  {xiOverRadiusRaw : ℤ → Spatial → PhysicalValue 1}
  (data : OriginalNativeMoments parameters covariantRaw xiOverRadiusRaw) (scale : Scale)

/-- The SAME covariant a_C=F_C^T U in the scaled coordinates. -/
def OriginalNativeMoments.scaledCovariant : StartupMoments 3 := data.covariant.dilate scale

/-- Fixed Q0 is applied to the covariant, before physical recovery by F_C^-T. -/
def OriginalNativeMoments.scaledCircle : StartupMoments 3 := (data.scaledCovariant scale).circle

def OriginalNativeMoments.scaledXiOverRadius : StartupMoments 1 := data.xiOverRadius.dilate scale

/-- Literal psi(Y)=Xi(ell Y)/ell, reconstructed directly from native Xi/r. -/
def OriginalNativeMoments.scaledPsi : StartupMoments 1 := (data.scaledXiOverRadius scale).radiusMultiply

def OriginalNativeMoments.scaledTheta : StartupMoments 1 := (data.scaledPsi scale).scalarInverse

theorem OriginalNativeMoments.scaledCircle_same :
    (data.scaledCircle scale).field = originalCircleKernel (data.scaledCovariant scale).field := rfl

theorem OriginalNativeMoments.scaledTheta_same :
    (data.scaledTheta scale).field = originalScalarInverseKernel (data.scaledPsi scale).field := rfl

theorem OriginalNativeMoments.scaledCovariant_same :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (data.scaledCovariant scale).field point cell =
        Grad.AnalyticWeights.Calculus.physicalWeight parameters.sigma0 parameters.gamma scale.val cell point •
          covariantRaw cell (scale.val • point) :=
  startupMomentDilation_weighted_same parameters.sigma0 parameters.gamma scale covariantRaw data.covariant.field data.covariant_same

theorem OriginalNativeMoments.scaledXiOverRadius_same :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (data.scaledXiOverRadius scale).field point cell =
        Grad.AnalyticWeights.Calculus.physicalWeight parameters.sigma0 parameters.gamma scale.val cell point •
          xiOverRadiusRaw cell (scale.val • point) :=
  startupMomentDilation_weighted_same parameters.sigma0 parameters.gamma scale xiOverRadiusRaw data.xiOverRadius.field data.xiOverRadius_same

theorem OriginalNativeMoments.scaledPsi_same :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (data.scaledPsi scale).field point cell =
        Grad.AnalyticWeights.Calculus.physicalWeight parameters.sigma0 parameters.gamma scale.val cell point •
          (‖point‖ • xiOverRadiusRaw cell (scale.val • point)) :=
  startupRadiusMultiply_dilation_weighted parameters.sigma0 parameters.gamma scale xiOverRadiusRaw data.xiOverRadius.field data.xiOverRadius_same

theorem OriginalNativeMoments.scaledPsi_originalXi :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (data.scaledPsi scale).field point cell =
        Grad.AnalyticWeights.Calculus.physicalWeight parameters.sigma0 parameters.gamma scale.val cell point •
          (scale.val⁻¹ • (‖scale.val • point‖ • xiOverRadiusRaw cell (scale.val • point))) := by
  filter_upwards [data.scaledPsi_same scale] with point same
  intro cell
  rw [scaledXi_fromRadius]
  exact same cell

theorem OriginalNativeMoments.scaledCovariant_norm (grade : Fin 3) :
    ‖(data.scaledCovariant scale).moment grade‖ ≤ scale.val⁻¹ * ‖data.covariant.moment grade‖ :=
  startupMomentDilation_norm _ _

theorem OriginalNativeMoments.scaledPsi_norm (grade : Fin 3) :
    ‖(data.scaledPsi scale).moment grade‖ ≤ scale.val⁻¹ * ‖data.xiOverRadius.moment grade‖ :=
  (startupRadiusMultiply_norm _).trans (startupMomentDilation_norm _ _)

theorem OriginalNativeMoments.scaledCircle_norm (grade : Fin 3) :
    ‖(data.scaledCircle scale).moment grade‖ ≤ ‖originalCircleKernel‖ *
      (scale.val⁻¹ * ‖data.covariant.moment grade‖) :=
  ((data.scaledCovariant scale).map_norm originalCircleKernel originalCircleKernel_cellwise grade).trans
    (mul_le_mul_of_nonneg_left (data.scaledCovariant_norm scale grade) (norm_nonneg _))

theorem OriginalNativeMoments.scaledTheta_norm (grade : Fin 3) :
    ‖(data.scaledTheta scale).moment grade‖ ≤ ‖originalScalarInverseKernel‖ *
      (scale.val⁻¹ * ‖data.xiOverRadius.moment grade‖) :=
  ((data.scaledPsi scale).map_norm originalScalarInverseKernel originalScalarInverseKernel_cellwise grade).trans
    (mul_le_mul_of_nonneg_left (data.scaledPsi_norm scale grade) (norm_nonneg _))

end Grad.CartesianStartup
