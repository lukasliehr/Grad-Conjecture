import AKBT21ActualOriginalERRows
import AKBS5ActualNormalizedSourceFirst

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.WeightedJets Grad.SpatialDilation
open Grad.AnalyticWeights.Calculus Grad.ActualOriginalSourceMoments Grad.ActualOriginalSourceFirst

/-- Two literal SAME native representatives supply the actual scaled
phase relation, with no coefficient/frequency interchange. -/
theorem sameScaledNative_phase {dimension : ℕ} (parameters : PhaseParameters) (scale : Scale)
    (weighted raw : StartupL2 dimension) (literal : ℤ → Spatial → PhysicalValue dimension)
    (weightedSame : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      weighted point cell = physicalWeight parameters.sigma0 parameters.gamma scale.val cell point • literal cell (scale.val • point))
    (rawSame : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, raw point cell = literal cell point) :
    StartupRadialRelated (physicalWeight parameters.sigma0 parameters.gamma scale.val) weighted (startupMomentDilation scale raw) := by
  filter_upwards [weightedSame,startupDilation_pull_ae scale _ rawSame,startupMomentDilation_ae scale raw]
    with point weightedAt rawAt dilated
  intro cell
  rw [weightedAt cell,dilated,rawAt cell]

theorem originalKnownSource_scaledPhase {dimension : ℕ} (parameters : PhaseParameters)
    (source : ACore parameters dimension) (scale : Scale) :
    StartupRadialRelated (physicalWeight parameters.sigma0 parameters.gamma scale.val)
      ((originalSourceMoments parameters source).dilate scale).field
      ((originalSourceRawMoments parameters source).dilate scale).field :=
  sameScaledNative_phase parameters scale _ _ _
    (startupMomentDilation_weighted_same parameters.sigma0 parameters.gamma scale _ _ (originalSourceMoments_same parameters source))
    (originalSourceRawMoments_same parameters source)

/-- The genuine known force's first graph includes the original Qrad.
Only the known source is differentiated here. -/
theorem originalKnownForce_qradFirst (parameters : PhaseParameters)
    (source : Grad.QuotientProjection.SmoothQuotient parameters) (length : ℝ) (positive : 0 < length) :
    base 2 1 openUnitDisk (fun _ => 0)
      (startupGenuineQradFirst (actualOriginalF_first parameters source length positive)) =
      ((((originalSourceMoments parameters (Grad.FlatSourceProjection.cartesianSourceVector source)).dilate
        (originalStartupScale length positive)).qrad).field) := by
  rw [startupGenuineQrad_compatible,actualOriginalF_first_base]
  rfl

end Grad.CartesianStartup
