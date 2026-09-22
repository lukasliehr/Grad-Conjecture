import AKBH1GenericMomentMultiplier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.CartesianState Grad.SpatialDilation
open Grad.AnalyticWeights.Calculus

/-- A globally bounded representative of the inverse original weight; on
our disk it is exactly the inverse weight, with unchanged sigma0 and gamma. -/
def startupInverseWeightSymbol (parameters : PhaseParameters) (scale : Scale) (cell : ℤ) (point : Spatial) : ℝ :=
  min 1 (inverseWeight parameters.sigma0 parameters.gamma scale.val cell point)

theorem startupInverseWeightSymbol_bound (parameters : PhaseParameters) (scale : Scale) (cell : ℤ) (point : Spatial) :
    |startupInverseWeightSymbol parameters scale cell point| ≤ 1 := by
  have nonnegative : 0 ≤ inverseWeight parameters.sigma0 parameters.gamma scale.val cell point := by
    rw [inverseWeight_exp]
    exact (Real.exp_pos _).le
  rw [startupInverseWeightSymbol,abs_of_nonneg (le_min zero_le_one nonnegative)]
  exact min_le_left _ _

theorem startupInverseWeightSymbol_measurable (parameters : PhaseParameters) (scale : Scale) (cell : ℤ) :
    AEStronglyMeasurable (startupInverseWeightSymbol parameters scale cell) (volume.restrict openUnitDisk) :=
  (continuous_const.min (smoothGoal parameters.sigma0 parameters.gamma scale.val cell).2.2.continuous).aestronglyMeasurable

theorem startupInverseWeightSymbol_same (parameters : PhaseParameters) (scale : Scale)
    (cell : ℤ) (point : Spatial) (inside : point ∈ openUnitDisk) :
    startupInverseWeightSymbol parameters scale cell point = inverseWeight parameters.sigma0 parameters.gamma scale.val cell point := by
  have scaledInside : ‖scale.val • point‖ ≤ 1 := by
    rw [norm_smul,Real.norm_of_nonneg scale.property.1.le]
    exact (mul_le_of_le_one_left (norm_nonneg point) scale.property.2).trans inside.le
  have weightOne := cartesianWeight_one_le parameters cell ⟨scale.val • point,scaledInside⟩
  change 1 ≤ physicalWeight parameters.sigma0 parameters.gamma 1 cell (scale.val • point) at weightOne
  rw [← startupPhysicalWeight_dilation parameters.sigma0 parameters.gamma scale.val scale.property.1.le] at weightOne
  exact min_eq_right (inv_le_one_of_one_le₀ weightOne)

def StartupMoments.unweight {dimension : ℕ} (family : StartupMoments dimension)
    (parameters : PhaseParameters) (scale : Scale) : StartupMoments dimension :=
  family.diagonal (startupInverseWeightSymbol parameters scale) 1 zero_le_one
    (startupInverseWeightSymbol_bound parameters scale) (startupInverseWeightSymbol_measurable parameters scale)

theorem StartupMoments.unweight_ae {dimension : ℕ} (family : StartupMoments dimension)
    (parameters : PhaseParameters) (scale : Scale) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (family.unweight parameters scale).field point cell =
        inverseWeight parameters.sigma0 parameters.gamma scale.val cell point • family.field point cell := by
  filter_upwards [startupMomentDiagonalField_ae (startupInverseWeightSymbol parameters scale) 1 zero_le_one
    (startupInverseWeightSymbol_bound parameters scale) (startupInverseWeightSymbol_measurable parameters scale) family.field,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point same inside
  intro cell
  change startupMomentDiagonalField (startupInverseWeightSymbol parameters scale) 1 zero_le_one
    (startupInverseWeightSymbol_bound parameters scale) (startupInverseWeightSymbol_measurable parameters scale) family.field point cell = _
  rw [same cell,startupInverseWeightSymbol_same parameters scale cell point inside,RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

theorem StartupMoments.unweight_norm {dimension : ℕ} (family : StartupMoments dimension)
    (parameters : PhaseParameters) (scale : Scale) (grade : Fin 3) :
    ‖(family.unweight parameters scale).moment grade‖ ≤ ‖family.moment grade‖ := by
  exact (startupMomentDiagonalField_norm (startupInverseWeightSymbol parameters scale) 1 zero_le_one
    (startupInverseWeightSymbol_bound parameters scale) (startupInverseWeightSymbol_measurable parameters scale)
    (family.moment grade)).trans_eq (one_mul _)

/-- The actual conjugated carrier gives the SAME unweighted field and
retains all three frequency moments. -/
theorem StartupMoments.unweight_same {dimension : ℕ} (family : StartupMoments dimension)
    (parameters : PhaseParameters) (scale : Scale) (raw : ℤ → Spatial → PhysicalValue dimension)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      family.field point cell = physicalWeight parameters.sigma0 parameters.gamma scale.val cell point • raw cell point) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (family.unweight parameters scale).field point cell = raw cell point := by
  filter_upwards [family.unweight_ae parameters scale,same] with point unweighted weighted
  intro cell
  rw [unweighted cell,weighted cell,smul_smul]
  have inverse : inverseWeight parameters.sigma0 parameters.gamma scale.val cell point *
      physicalWeight parameters.sigma0 parameters.gamma scale.val cell point = 1 := by
    rw [mul_comm]
    exact (formulaGoal _ _ _ _ _).2.2.2.2
  rw [inverse,one_smul]

end Grad.CartesianStartup
