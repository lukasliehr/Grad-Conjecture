import AKO5SameHighMovingIncomingTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped ENNReal BigOperators
namespace Grad.AnnularIncomingIntegrability
open Grad.ClosedJets Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularLowEnergy
open Grad.AnnularSourceGraph Grad.AnnularRestriction Grad.GaugeCoefficients.Physical.WeightedTrace

variable (lower upper length : ℝ) (lowerPositive : 0 < lower) (upperPositive : 0 < upper)
    (upperBounded : upper < 1) (included : lower ≤ upper)

theorem lowIncomingTrace_restricted_section (field : lowEnergyGraph lower length lowerPositive) (index : LowAnnularIndex) :
    lowEnergyEndpoint upper length upperPositive upperBounded 0
      (lowEnergyRestriction lower upper length included lowerPositive upperPositive upperBounded field) index =
      lowIncomingRepresentative lower length lowerPositive (included.trans_lt upperBounded) field index upper := by
  have sections := congrArg (fun value : RadialContinuousSection 1 upper => value ⟨upper,le_rfl,upperBounded.le⟩)
    (lowEnergyRestriction_section lower upper length included lowerPositive upperPositive upperBounded field index)
  have extended : lowIncomingRepresentative lower length lowerPositive (included.trans_lt upperBounded) field index upper =
      lowEnergySection lower length lowerPositive (included.trans_lt upperBounded) field index ⟨upper,included,upperBounded.le⟩ := by
    change lowEnergySection lower length lowerPositive (included.trans_lt upperBounded) field index
      (radialClamp lower (included.trans_lt upperBounded).le upper) = _
    rw [radialClamp_eq lower (included.trans_lt upperBounded).le upper ⟨included,upperBounded.le⟩]
  exact sections.trans extended.symm

/-- The integrated low density is exactly the moving BF incoming norm,
including both low components and every cell. -/
theorem lowIncomingSquare_eq_restricted_norm (field : lowEnergyGraph lower length lowerPositive) :
    lowIncomingSquare lower length lowerPositive (included.trans_lt upperBounded) field upper =
      ENNReal.ofReal (‖lowIncomingTrace upper length upperPositive upperBounded
        (lowEnergyRestriction lower upper length included lowerPositive upperPositive upperBounded field)‖ ^ 2) := by
  let trace := lowIncomingTrace upper length upperPositive upperBounded
    (lowEnergyRestriction lower upper length included lowerPositive upperPositive upperBounded field)
  have normSum : ‖trace‖ ^ 2 = ∑' index, ‖trace index‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using (lp.norm_rpow_eq_tsum (p := 2) (by norm_num) trace)
  change (∑' index : LowAnnularIndex, ENNReal.ofReal _) = ENNReal.ofReal (‖trace‖ ^ 2)
  rw [normSum,ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (lp_summable_sq trace)]
  apply tsum_congr
  intro index
  have normCoordinate := lowIncomingCoefficient_norm_sq upper length upperPositive upperBounded
    (lowEnergyRestriction lower upper length included lowerPositive upperPositive upperBounded field) index
  exact congrArg ENNReal.ofReal ((congrArg (fun value : ComplexEuclidean 1 =>
    upper ^ (-(7 / 2 : ℝ)) * (lowMu length upper index.2.val.2)⁻¹ * ‖value‖ ^ 2)
    (lowIncomingTrace_restricted_section lower upper length lowerPositive upperPositive upperBounded included field index)).symm.trans normCoordinate.symm)

end Grad.AnnularIncomingIntegrability
