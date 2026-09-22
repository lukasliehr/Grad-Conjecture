import AJW4HighRestrictedCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped Topology
namespace Grad.AnnularRestriction
open Grad.AnnularVariational Grad.AnnularOmegaGraph Grad.AnnularCrossMaps Grad.AnnularOriginalHigh

/-- Literal restriction of the actual weighted high energy/flux pair. -/
def highWeightedRestriction (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper) :
    CrossHighSpace lower length lowerPositive lengthPositive →L[ℂ]
      CrossHighSpace upper length upperPositive lengthPositive :=
  restrictionPairMap (highEnergyRestriction lower upper length lowerPositive upperPositive included)
    (highOmegaRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included)

theorem highWeightedRestriction_bound (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (field : CrossHighSpace lower length lowerPositive lengthPositive) :
    ‖highWeightedRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field‖ ≤ ‖field‖ :=
  restrictionPairMap_norm_le
    (highEnergyRestriction lower upper length lowerPositive upperPositive included)
    (highOmegaRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included)
    (highEnergyRestriction_bound lower upper length lowerPositive upperPositive included)
    (highOmegaRestriction_bound lower upper length lowerPositive upperPositive upperBounded lengthPositive included) field

/-- V1's exact endpoint-changing retained high map: Psi_upper inverse,
literal weighted restriction, then Psi_lower. -/
def originalHighRestriction (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper) :
    OriginalHighSpace lower length lowerPositive →L[ℂ] OriginalHighSpace upper length upperPositive :=
  (originalHighTiltEquivalence upper length upperPositive upperBounded.le lengthPositive).symm.toContinuousLinearMap.comp
    ((highWeightedRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included).comp
      (originalHighTiltEquivalence lower length lowerPositive (included.trans upperBounded.le) lengthPositive).toContinuousLinearMap)

theorem originalHighRestriction_weighted (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (field : OriginalHighSpace lower length lowerPositive) :
    originalHighTiltEquivalence upper length upperPositive upperBounded.le lengthPositive
      (originalHighRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field) =
    highWeightedRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included
      (originalHighTiltEquivalence lower length lowerPositive (included.trans upperBounded.le) lengthPositive field) :=
  (originalHighTiltEquivalence upper length upperPositive upperBounded.le lengthPositive).apply_symm_apply _

/-- Only fixed-endpoint continuity is asserted here; this constant is not
an exhaustion estimate uniform as the lower endpoint tends to zero. -/
theorem originalHighRestriction_bound (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (field : OriginalHighSpace lower length lowerPositive) :
    ‖originalHighRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field‖ ≤
      (‖(originalHighTiltEquivalence upper length upperPositive upperBounded.le lengthPositive).symm.toContinuousLinearMap‖ *
        ‖(originalHighTiltEquivalence lower length lowerPositive (included.trans upperBounded.le) lengthPositive).toContinuousLinearMap‖) * ‖field‖ := by
  let inverse := (originalHighTiltEquivalence upper length upperPositive upperBounded.le lengthPositive).symm.toContinuousLinearMap
  let forward := (originalHighTiltEquivalence lower length lowerPositive (included.trans upperBounded.le) lengthPositive).toContinuousLinearMap
  let restricted := highWeightedRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included
  change ‖inverse (restricted (forward field))‖ ≤ (‖inverse‖ * ‖forward‖) * ‖field‖
  calc
    _ ≤ ‖inverse‖ * ‖restricted (forward field)‖ := inverse.le_opNorm _
    _ ≤ ‖inverse‖ * ‖forward field‖ := mul_le_mul_of_nonneg_left
      (highWeightedRestriction_bound lower upper length lowerPositive upperPositive upperBounded lengthPositive included (forward field)) (norm_nonneg inverse)
    _ ≤ ‖inverse‖ * (‖forward‖ * ‖field‖) := mul_le_mul_of_nonneg_left (forward.le_opNorm field) (norm_nonneg inverse)
    _ = _ := (mul_assoc _ _ _).symm

end Grad.AnnularRestriction
