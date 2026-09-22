import AED2InversePowerPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.AnnularTiltedReference
open Grad.ClosedJets Grad.AnnularVariational Grad.AnnularReconstruction Grad.SourceCollarDivision
open Grad.CartesianState Grad.CircularHighRegularity Grad.AnnularHighTilt Grad.AnnularFluxTrace

section Transport
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem highEnergyUnweight_phase (field : annularEnergySpace lower length positive) :
    annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength (highEnergyUnweight lower length positive bounded field) =
      highBulkUnweight lower positive bounded (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field) := by
  apply lp.ext
  funext mode
  change annularPhaseMassMap parameters lower length positive lengthPositive widthHalf widthLength mode
    (annularEnergyMass lower length positive (highEnergyUnweight lower length positive bounded field) mode) = _
  rw [highEnergyUnweight_mass_apply]
  exact scalarRadialMap_comm lower (annularPhaseMassRatio parameters lower length positive mode)
    (highPowerCurve lower highTiltExponent positive) (1 / 2) 1
    (annularPhaseMassRatio_bound parameters lower length positive lengthPositive widthHalf widthLength mode) (highPositivePower_bound lower positive bounded) _

theorem highEnergyUnweight_mass (field : annularEnergySpace lower length positive) :
    annularEnergyMass lower length positive (highEnergyUnweight lower length positive bounded field) =
      highBulkUnweight lower positive bounded (annularEnergyMass lower length positive field) := by
  apply lp.ext
  funext mode
  exact highEnergyUnweight_mass_apply lower length positive bounded field mode

theorem highEnergyUnweight_outer (field : annularEnergySpace lower length positive) :
    annularEnergyOuter lower length positive (highEnergyUnweight lower length positive bounded field) =
      annularEnergyOuter lower length positive field := by
  apply lp.ext
  funext mode
  exact highEnergyUnweight_outer_apply lower length positive bounded field mode

/-- Exact opposite derivative under the actual radial power. -/
theorem highEnergyUnweight_phaseDerivative (field : annularEnergySpace lower length positive) :
    annularEnergyDerivative lower length positive (highEnergyUnweight lower length positive bounded field) -
      annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength (highEnergyUnweight lower length positive bounded field) =
      highBulkUnweight lower positive bounded
        (annularEnergyDerivative lower length positive field - annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field) := by
  rw [highEnergyUnweight_phase parameters lower length positive bounded lengthPositive widthHalf widthLength]
  apply lp.ext
  funext mode
  change annularEnergyDerivative lower length positive (highEnergyUnweight lower length positive bounded field) mode -
    (highBulkUnweight lower positive bounded (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)) mode = _
  rw [highEnergyUnweight_derivative_apply]
  have coefficient : ∀ radius ∈ Icc lower 1,
      highEnergySlopeRatio lower length highTiltExponent positive mode radius =
        highPowerCurve lower highTiltExponent positive radius *
          ((annularPhaseMassRatio parameters lower length positive mode) radius - (annularTiltPhaseRatio parameters lower length positive mode) radius) := by
    intro radius inside
    change highPowerSlopeCurve lower highTiltExponent positive radius /
      annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius = _
    rw [highPowerSlope_logarithmic lower highTiltExponent positive radius inside]
    change (highPowerCurve lower highTiltExponent positive radius * ((9 / 4 : ℝ) / max lower radius)) /
      (annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius) = highPowerCurve lower highTiltExponent positive radius *
        ((annularPhaseSlope parameters mode.val.2 radius) / (annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius) - ((annularPhaseSlope parameters mode.val.2 radius - (9 / 4 : ℝ) / max lower radius)) / (annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius))
    ring
  have slope := scalarRadialMap_difference_product lower
    (highEnergySlopeRatio lower length highTiltExponent positive mode)
    (highPowerCurve lower highTiltExponent positive)
    (annularPhaseMassRatio parameters lower length positive mode) (annularTiltPhaseRatio parameters lower length positive mode) (highTiltExponent / 3) 1 (1 / 2) (Real.sqrt (15 / 16))
    (highEnergyPositiveSlope_bound lower length positive bounded mode) (highPositivePower_bound lower positive bounded) (annularPhaseMassRatio_bound parameters lower length positive lengthPositive widthHalf widthLength mode) (annularTiltPhaseRatio_bound parameters lower length positive lengthPositive widthHalf widthLength mode) coefficient
    (annularEnergyMass lower length positive field mode)
  change scalarRadialMap lower (highPowerCurve lower highTiltExponent positive) 1 (highPositivePower_bound lower positive bounded)
      (annularEnergyDerivative lower length positive field mode) +
    scalarRadialMap lower (highEnergySlopeRatio lower length highTiltExponent positive mode) (highTiltExponent / 3) (highEnergyPositiveSlope_bound lower length positive bounded mode)
      (annularEnergyMass lower length positive field mode) -
    scalarRadialMap lower (highPowerCurve lower highTiltExponent positive) 1 (highPositivePower_bound lower positive bounded)
      (annularPhaseMassMap parameters lower length positive lengthPositive widthHalf widthLength mode
        (annularEnergyMass lower length positive field mode)) =
    scalarRadialMap lower (highPowerCurve lower highTiltExponent positive) 1 (highPositivePower_bound lower positive bounded)
      (annularEnergyDerivative lower length positive field mode -
        annularTiltPhaseMap parameters lower length positive lengthPositive widthHalf widthLength mode
          (annularEnergyMass lower length positive field mode))
  rw [slope, map_sub, map_sub]
  dsimp only [annularPhaseMassMap, annularTiltPhaseMap]
  abel

theorem highEnergyWeight_phase (field : annularEnergySpace lower length positive) :
    annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength (highEnergyWeight lower length positive bounded field) =
      highBulkWeight lower positive bounded (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field) := by
  apply lp.ext
  funext mode
  change annularPhaseMassMap parameters lower length positive lengthPositive widthHalf widthLength mode
    (annularEnergyMass lower length positive (highEnergyWeight lower length positive bounded field) mode) = _
  rw [highEnergyWeight_mass_apply]
  exact scalarRadialMap_comm lower (annularPhaseMassRatio parameters lower length positive mode)
    (highPowerCurve lower (-highTiltExponent) positive) (1 / 2) (lower ^ (-highTiltExponent))
    (annularPhaseMassRatio_bound parameters lower length positive lengthPositive widthHalf widthLength mode) (highNegativePower_bound lower positive bounded) _

theorem highEnergyWeight_mass (field : annularEnergySpace lower length positive) :
    annularEnergyMass lower length positive (highEnergyWeight lower length positive bounded field) =
      highBulkWeight lower positive bounded (annularEnergyMass lower length positive field) := by
  apply lp.ext
  funext mode
  exact highEnergyWeight_mass_apply lower length positive bounded field mode

theorem highEnergyWeight_outer (field : annularEnergySpace lower length positive) :
    annularEnergyOuter lower length positive (highEnergyWeight lower length positive bounded field) =
      annularEnergyOuter lower length positive field := by
  apply lp.ext
  funext mode
  exact highEnergyWeight_outer_apply lower length positive bounded field mode

/-- Exact opposite derivative under the actual radial power. -/
theorem highEnergyWeight_phaseDerivative (field : annularEnergySpace lower length positive) :
    annularEnergyDerivative lower length positive (highEnergyWeight lower length positive bounded field) +
      annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength (highEnergyWeight lower length positive bounded field) =
      highBulkWeight lower positive bounded
        (annularEnergyDerivative lower length positive field + annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field) := by
  rw [highEnergyWeight_phase parameters lower length positive bounded lengthPositive widthHalf widthLength]
  apply lp.ext
  funext mode
  change annularEnergyDerivative lower length positive (highEnergyWeight lower length positive bounded field) mode +
    (highBulkWeight lower positive bounded (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)) mode = _
  rw [highEnergyWeight_derivative_apply]
  have coefficient : ∀ radius ∈ Icc lower 1,
      highEnergySlopeRatio lower length (-highTiltExponent) positive mode radius =
        highPowerCurve lower (-highTiltExponent) positive radius *
          ((annularTiltPhaseRatio parameters lower length positive mode) radius - (annularPhaseMassRatio parameters lower length positive mode) radius) := by
    intro radius inside
    change highPowerSlopeCurve lower (-highTiltExponent) positive radius /
      annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius = _
    rw [highPowerSlope_logarithmic lower (-highTiltExponent) positive radius inside]
    change (highPowerCurve lower (-highTiltExponent) positive radius * ((-(9 / 4 : ℝ)) / max lower radius)) /
      (annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius) = highPowerCurve lower (-highTiltExponent) positive radius *
        (((annularPhaseSlope parameters mode.val.2 radius - (9 / 4 : ℝ) / max lower radius)) / (annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius) - (annularPhaseSlope parameters mode.val.2 radius) / (annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius))
    ring
  have slope := scalarRadialMap_difference_product lower
    (highEnergySlopeRatio lower length (-highTiltExponent) positive mode)
    (highPowerCurve lower (-highTiltExponent) positive)
    (annularTiltPhaseRatio parameters lower length positive mode) (annularPhaseMassRatio parameters lower length positive mode) (highTiltExponent / 3 * lower ^ (-highTiltExponent)) (lower ^ (-highTiltExponent)) (Real.sqrt (15 / 16)) (1 / 2)
    (highEnergyNegativeSlope_bound lower length positive bounded mode) (highNegativePower_bound lower positive bounded) (annularTiltPhaseRatio_bound parameters lower length positive lengthPositive widthHalf widthLength mode) (annularPhaseMassRatio_bound parameters lower length positive lengthPositive widthHalf widthLength mode) coefficient
    (annularEnergyMass lower length positive field mode)
  change scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive) (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded)
      (annularEnergyDerivative lower length positive field mode) +
    scalarRadialMap lower (highEnergySlopeRatio lower length (-highTiltExponent) positive mode) (highTiltExponent / 3 * lower ^ (-highTiltExponent)) (highEnergyNegativeSlope_bound lower length positive bounded mode)
      (annularEnergyMass lower length positive field mode) +
    scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive) (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded)
      (annularPhaseMassMap parameters lower length positive lengthPositive widthHalf widthLength mode
        (annularEnergyMass lower length positive field mode)) =
    scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive) (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded)
      (annularEnergyDerivative lower length positive field mode +
        annularTiltPhaseMap parameters lower length positive lengthPositive widthHalf widthLength mode
          (annularEnergyMass lower length positive field mode))
  rw [slope, map_sub, map_add]
  dsimp only [annularPhaseMassMap, annularTiltPhaseMap]
  abel

end Transport
end Grad.AnnularTiltedReference
