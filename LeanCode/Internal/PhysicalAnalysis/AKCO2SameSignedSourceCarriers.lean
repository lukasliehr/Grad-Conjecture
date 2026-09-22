import AKCO1ActualSignedSourceFirst

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory
namespace Grad.ActualOriginalSourceFirst
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.CartesianStartup
open Grad.ActualScalarWeakEquations Grad.SpatialDilation Grad.WeightedJets

variable {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)
  (L : ℝ) (scale : Scale)

/-- Exact signed moment of the SAME scaled original source, including its
unchanged physical phase; every power has an actual first weak graph. -/
theorem originalSignedAxialFirst_same (power : ℕ) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      base dimension 1 openUnitDisk (fun _ => 0)
        (originalSignedAxialFirst parameters field L scale power) point cell =
      startupAxialFrequency L scale.val cell ^ power •
        base dimension 1 openUnitDisk (fun _ => 0)
          (scaledOriginalSourceFirst parameters field scale) point cell := by
  filter_upwards [scaledOriginalSourceFirst_same parameters
    (originalSignedAxialCore parameters field L scale.val power) scale,
    scaledOriginalSourceFirst_same parameters field scale,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point momentSame fieldSame inside
  intro cell
  rw [originalSignedAxialFirst,momentSame cell,fieldSame cell]
  have scaledInside : scale.val • point ∈ openUnitDisk := startupDilation_inclusion scale inside
  let closed : ClosedDisk := ⟨scale.val • point,openDiskMembershipClosed _ scaledInside⟩
  rw [originalSignedAxialCore_cell parameters field L scale.val power cell closed]
  exact smul_comm _ _ _

/-- The exact projection premise used by the accepted full-cell binomial
identity. No unknown-source or output-moment premise appears. -/
theorem originalSignedAxialFirst_projection (power : ℕ) (cell : ℤ) :
    fieldCellProjection dimension openUnitDisk cell
      (base dimension 1 openUnitDisk (fun _ => 0)
        (originalSignedAxialFirst parameters field L scale power)) =
      startupAxialFrequency L scale.val cell ^ power •
        fieldCellProjection dimension openUnitDisk cell
          (base dimension 1 openUnitDisk (fun _ => 0)
            (scaledOriginalSourceFirst parameters field scale)) := by
  apply Lp.ext
  filter_upwards [originalSignedAxialFirst_same parameters field L scale power,
    fieldCellProjection_ae dimension openUnitDisk
      (base dimension 1 openUnitDisk (fun _ => 0) (originalSignedAxialFirst parameters field L scale power)),
    fieldCellProjection_ae dimension openUnitDisk
      (base dimension 1 openUnitDisk (fun _ => 0) (scaledOriginalSourceFirst parameters field scale)),
    Lp.coeFn_smul (startupAxialFrequency L scale.val cell ^ power)
      (fieldCellProjection dimension openUnitDisk cell
        (base dimension 1 openUnitDisk (fun _ => 0) (scaledOriginalSourceFirst parameters field scale)))]
      with point same one two scaled
  rw [one cell,scaled,Pi.smul_apply,two cell,same cell]

theorem originalSignedAxialFirst_zero :
    originalSignedAxialFirst parameters field L scale 0 =
      scaledOriginalSourceFirst parameters field scale := rfl

end Grad.ActualOriginalSourceFirst
