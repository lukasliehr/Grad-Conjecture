import AKCO12SameNaturalMomentReserves
import AKCO10SameSignedWeakEREquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.CartesianState Grad.WeightedJets
open Grad.AnalyticWeights.Calculus Grad.SpatialDilation
namespace StartupSignedFamily
variable {dimension : ℕ} {L ell : ℝ}

def diagonal (family : StartupSignedFamily dimension L ell)
    (symbol : ℤ → Spatial → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ cell point, |symbol cell point| ≤ constant)
    (measurable : ∀ cell, AEStronglyMeasurable (symbol cell) (volume.restrict openUnitDisk)) :
    StartupSignedFamily dimension L ell where
  field := startupMomentDiagonalField symbol constant nonnegative bounded measurable family.field
  moment power := startupMomentDiagonalField symbol constant nonnegative bounded measurable (family.moment power)
  same power := by
    filter_upwards [startupMomentDiagonalField_ae symbol constant nonnegative bounded measurable family.field,
      startupMomentDiagonalField_ae symbol constant nonnegative bounded measurable (family.moment power),family.same power]
      with point fieldAt momentAt same
    intro cell
    rw [momentAt cell,fieldAt cell,same cell]
    exact smul_comm _ _ _

def unweight (parameters : PhaseParameters) (scale : Scale)
    (family : StartupSignedFamily dimension L scale.val) : StartupSignedFamily dimension L scale.val :=
  family.diagonal (startupInverseWeightSymbol parameters scale) 1 zero_le_one
    (startupInverseWeightSymbol_bound parameters scale) (startupInverseWeightSymbol_measurable parameters scale)

theorem unweight_moment (parameters : PhaseParameters) (scale : Scale)
    (family : StartupSignedFamily dimension L scale.val) (power : ℕ) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (family.unweight parameters scale).moment power point cell =
        inverseWeight parameters.sigma0 parameters.gamma scale.val cell point • family.moment power point cell := by
  filter_upwards [startupMomentDiagonalField_ae (startupInverseWeightSymbol parameters scale) 1 zero_le_one
    (startupInverseWeightSymbol_bound parameters scale) (startupInverseWeightSymbol_measurable parameters scale)
    (family.moment power),ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point same inside
  intro cell
  change startupMomentDiagonalField (startupInverseWeightSymbol parameters scale) 1 zero_le_one
    (startupInverseWeightSymbol_bound parameters scale)
    (startupInverseWeightSymbol_measurable parameters scale) (family.moment power) point cell = _
  rw [same cell,startupInverseWeightSymbol_same parameters scale cell point inside,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

theorem unweight_field (parameters : PhaseParameters) (scale : Scale)
    (family : StartupSignedFamily dimension L scale.val) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (family.unweight parameters scale).field point cell =
        inverseWeight parameters.sigma0 parameters.gamma scale.val cell point • family.field point cell := by
  have same := family.unweight_moment parameters scale 0
  rw [family.zero,(family.unweight parameters scale).zero] at same
  exact same

/-- Every signed power has its SAME original phase relation. -/
theorem unweight_phase (parameters : PhaseParameters) (scale : Scale)
    (family : StartupSignedFamily dimension L scale.val) (power : ℕ) :
    StartupRadialRelated (physicalWeight parameters.sigma0 parameters.gamma scale.val)
      (family.moment power) ((family.unweight parameters scale).moment power) := by
  filter_upwards [family.unweight_moment parameters scale power] with point same
  intro cell
  rw [same cell,smul_smul,(formulaGoal _ _ _ _ _).2.2.2.2,one_smul]

/-- The unweighted base is identified with the existing native raw
representative solely from its already proved actual phase equality. -/
theorem unweight_sameBase (parameters : PhaseParameters) (scale : Scale)
    (family : StartupSignedFamily dimension L scale.val) (raw : StartupL2 dimension)
    (phase : StartupRadialRelated (physicalWeight parameters.sigma0 parameters.gamma scale.val) family.field raw) :
    (family.unweight parameters scale).field = raw := by
  apply Lp.ext
  filter_upwards [family.unweight_field parameters scale,phase] with point inverse same
  apply lp.ext
  funext cell
  rw [inverse cell,same cell,smul_smul,mul_comm,(formulaGoal _ _ _ _ _).2.2.2.2,one_smul]

end StartupSignedFamily
end Grad.CartesianStartup
