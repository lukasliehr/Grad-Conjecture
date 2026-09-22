import AKG19SameHighEightInputRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularRestriction
open Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational Grad.AnnularLowEnergy
open Grad.AnnularCrossMaps Grad.AnnularCoupledInverse Grad.AnnularStrongSolution Grad.AnnularCurrentLow

private theorem homogeneous_lowOnly (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length) (field : lowEnergyGraph lower length positive) :
    homogeneousCoupledSevenInput parameters length lower lengthPositive positive
      (WithLp.toLp 2 (0,field)) = lowNormalizedSevenInput parameters lower length lengthPositive positive (field.val 0) := by
  change highCrossSevenInput lower length positive lengthPositive 0 + _ = _
  rw [map_zero,zero_add]
  rfl

private theorem restriction_lowOnly (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper) (field : lowEnergyGraph lower length lowerPositive) :
    coupledEndpointRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included
      (WithLp.toLp 2 (0,field)) =
    WithLp.toLp 2 (0,lowEnergyRestriction lower upper length included lowerPositive upperPositive upperBounded field) := by
  change WithLp.toLp 2 (highWeightedRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included 0,
    lowEnergyRestriction lower upper length included lowerPositive upperPositive upperBounded field) = _
  rw [map_zero]

theorem lowNormalizedSevenInput_restriction (parameters : PhaseParameters) (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper) (field : lowEnergyGraph lower length lowerPositive) :
    originalBulkRestriction 7 lower upper included
      (lowNormalizedSevenInput parameters lower length lengthPositive lowerPositive (field.val 0)) =
    lowNormalizedSevenInput parameters upper length lengthPositive upperPositive
      ((lowEnergyRestriction lower upper length included lowerPositive upperPositive upperBounded field).val 0) := by
  exact (congrArg (originalBulkRestriction 7 lower upper included)
    (homogeneous_lowOnly parameters lower length lowerPositive lengthPositive field).symm).trans
      ((homogeneousCoupledSevenInput_restriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included
        (WithLp.toLp 2 (0,field))).trans
          ((congrArg (homogeneousCoupledSevenInput parameters length upper lengthPositive upperPositive)
            (restriction_lowOnly lower upper length lowerPositive upperPositive upperBounded lengthPositive included field)).trans
              (homogeneous_lowOnly parameters upper length upperPositive lengthPositive _)))

end Grad.AnnularRestriction
