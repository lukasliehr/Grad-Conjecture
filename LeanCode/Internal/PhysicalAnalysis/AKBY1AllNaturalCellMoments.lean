import AKBF12SameScaledStartupFields

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.CartesianState Grad.SpatialDilation

/-- One full integer-cell field with every natural frequency moment. -/
structure StartupAllMoments (dimension : ℕ) where
  field : StartupL2 dimension
  moment : ℕ → StartupL2 dimension
  zero : moment 0 = field
  same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ power : ℕ, ∀ cell : ℤ,
    moment power point cell = Grad.CellWeights.cellWeight cell ^ power • field point cell

def StartupAllMoments.firstThree {dimension : ℕ} (family : StartupAllMoments dimension) : StartupMoments dimension where
  field := family.field
  moment power := family.moment power.val
  zero := family.zero
  same := family.same.mono (fun _ same power => same power.val)

def StartupAllMoments.withField {dimension : ℕ} (family : StartupAllMoments dimension)
    (field : StartupL2 dimension) (equal : family.field = field) : StartupAllMoments dimension where
  field := field
  moment := family.moment
  zero := family.zero.trans equal
  same := by rw [← equal]; exact family.same

def StartupAllMoments.dilate {dimension : ℕ} (family : StartupAllMoments dimension) (scale : Scale) : StartupAllMoments dimension where
  field := startupMomentDilation scale family.field
  moment power := startupMomentDilation scale (family.moment power)
  zero := congrArg (startupMomentDilation scale) family.zero
  same := by
    apply ae_all_iff.mpr
    intro power
    exact startupMomentDilation_moment scale power family.field (family.moment power)
      (family.same.mono (fun _ same => same power))

def StartupAllMoments.radiusMultiply {dimension : ℕ} (family : StartupAllMoments dimension) : StartupAllMoments dimension where
  field := startupRadiusMultiply family.field
  moment power := startupRadiusMultiply (family.moment power)
  zero := congrArg startupRadiusMultiply family.zero
  same := by
    apply ae_all_iff.mpr
    intro power
    filter_upwards [startupRadiusMultiply_ae family.field,startupRadiusMultiply_ae (family.moment power),family.same]
      with point fieldAt momentAt same
    intro cell
    rw [momentAt,fieldAt]
    simp only [lp.coeFn_smul,Pi.smul_apply]
    rw [same power cell]
    exact smul_comm _ _ _

end Grad.CartesianStartup
