import AKCU7OriginalConstructedFamilySource
import NGP02Consumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set
open scoped ContDiff
namespace Grad.OriginalParameterEvaluation
open Grad.CartesianState Grad.ClosedJets Grad.DiskExtension.Operator

variable {dimension : ℕ} (parameters : PhaseParameters)

/-- Original unmodified Fourier coefficients, as one complex-linear map. -/
def originalCoefficientLinear : ACore parameters dimension →ₗ[ℂ] OrdinaryCoefficientCore dimension where
  toFun := originalCoefficientCore parameters
  map_add' first second := by apply Subtype.ext; rfl
  map_smul' scalar field := by apply Subtype.ext; rfl

/-- The SAME original physical closed jet, before the fixed collar extension. -/
def originalPhysicalJetLinear : ACore parameters dimension →ₗ[ℂ] DiskCellClosedJet dimension :=
  ordinaryReconstructedClosedJetLinear.comp (originalCoefficientLinear parameters)

theorem originalPhysicalJetLinear_apply (field : ACore parameters dimension) :
    originalPhysicalJetLinear parameters field=originalPhysicalClosedJet parameters field := rfl

/-- The one actual P09 extension of the original unmodified physical core. -/
def originalExtendedField (field : ACore parameters dimension) : SpatialCell → ComplexEuclidean dimension :=
  ambientExtensionCellLift (originalPhysicalClosedJet parameters field)

theorem originalExtendedField_smooth (field : ACore parameters dimension) :
    ContDiff ℝ ∞ (originalExtendedField parameters field) :=
  ambientExtensionCellLift_contDiff_infty (originalPhysicalClosedJet parameters field)

theorem originalExtendedField_add (first second : ACore parameters dimension) :
    originalExtendedField parameters (first+second)=originalExtendedField parameters first+originalExtendedField parameters second := by
  funext point
  change ambientExtensionFromValue (originalPhysicalJetLinear parameters (first+second)).value
    (planarPart point) (point 2 : CellCircle)=_
  rw [map_add]
  exact ambientExtension_add (originalPhysicalClosedJet parameters first) (originalPhysicalClosedJet parameters second)
    (planarPart point) (point 2 : CellCircle)

theorem originalExtendedField_smul (scalar : ℂ) (field : ACore parameters dimension) :
    originalExtendedField parameters (scalar • field)=scalar • originalExtendedField parameters field := by
  funext point
  change ambientExtensionFromValue (originalPhysicalJetLinear parameters (scalar • field)).value
    (planarPart point) (point 2 : CellCircle)=_
  rw [map_smul]
  exact ambientExtension_smul scalar (originalPhysicalClosedJet parameters field) (planarPart point) (point 2 : CellCircle)

/-- All closed-disk values remain the SAME original field. -/
theorem originalExtendedField_onDisk (field : ACore parameters dimension) (point : ClosedDisk) (cell : ℝ) :
    originalExtendedField parameters field (assembleSpatialCell point.val cell)=
      (originalPhysicalClosedJet parameters field).value (point,(cell : CellCircle)) := by
  unfold originalExtendedField ambientExtensionCellLift
  rw [planarPart_assembleSpatialCell]
  simpa [assembleSpatialCell] using
    ambientExtension_inside (originalPhysicalClosedJet parameters field).value point.val point.property (cell : CellCircle)

end Grad.OriginalParameterEvaluation
