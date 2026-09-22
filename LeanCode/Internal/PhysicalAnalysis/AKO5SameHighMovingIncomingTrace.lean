import AKO4ActualHighIncomingLogBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped ENNReal BigOperators
namespace Grad.AnnularIncomingIntegrability
open Grad.ClosedJets Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularRestriction
open Grad.AnnularTiltedReference Grad.GaugeCoefficients.Physical.WeightedTrace

variable (lower upper length : ℝ) (lowerPositive : 0 < lower) (upperPositive : 0 < upper)
    (upperBounded : upper < 1) (lengthPositive : 0 < length) (included : lower ≤ upper)

/-- Moving high incoming evaluation is exactly the genuine SAME H1 section. -/
theorem highIncomingTrace_restricted_coefficient (field : annularEnergySpace lower length lowerPositive) (mode : HighAnnularMode) :
    annularEnergyTrace upper length upperPositive upperBounded lengthPositive 0
      (bEnergyDecode upper length upperPositive (highEnergyRestriction lower upper length lowerPositive upperPositive included field)) mode =
    (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) •
      highIncomingRepresentative lower length lowerPositive (included.trans_lt upperBounded) field mode upper := by
  have sections := congrArg (fun value : RadialContinuousSection 1 upper => value ⟨upper,le_rfl,upperBounded.le⟩)
    (highEnergyRestriction_section lower upper length lowerPositive upperPositive upperBounded included
      (bEnergyDecode lower length lowerPositive field) mode)
  rw [highEnergyRestriction_bDecode lower upper length lowerPositive upperPositive upperBounded included] at sections
  have extended : highIncomingRepresentative lower length lowerPositive (included.trans_lt upperBounded) field mode upper =
      weightedRadialSection 1 lower lowerPositive (included.trans_lt upperBounded)
        (annularModeRadialH1 lower length lowerPositive mode (bEnergyDecode lower length lowerPositive field)) ⟨upper,included,upperBounded.le⟩ := by
    change weightedRadialSection 1 lower lowerPositive (included.trans_lt upperBounded)
      (annularModeRadialH1 lower length lowerPositive mode (bEnergyDecode lower length lowerPositive field))
      (radialClamp lower (included.trans_lt upperBounded).le upper) = _
    rw [radialClamp_eq lower (included.trans_lt upperBounded).le upper ⟨included,upperBounded.le⟩]
  exact (annularEnergyTrace_eq_radial upper length upperPositive upperBounded lengthPositive 0 mode _).trans
    (congrArg (fun value : ComplexEuclidean 1 => (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) • value)
      ((weightedRadialSection_endpoint 1 upper upperPositive upperBounded 0
        (annularModeRadialH1 upper length upperPositive mode
          (bEnergyDecode upper length upperPositive (highEnergyRestriction lower upper length lowerPositive upperPositive included field)))).symm.trans
            (sections.trans extended.symm)))

/-- The density already integrated is literally the BF incoming norm of the
restricted original field, with its original positive-half frequency weight. -/
theorem highIncomingSquare_eq_restricted_norm (field : annularEnergySpace lower length lowerPositive) :
    highIncomingSquare lower length lowerPositive (included.trans_lt upperBounded) field upper =
      ENNReal.ofReal (‖annularEnergyTrace upper length upperPositive upperBounded lengthPositive 0
        (bEnergyDecode upper length upperPositive (highEnergyRestriction lower upper length lowerPositive upperPositive included field))‖ ^ 2) := by
  let trace := annularEnergyTrace upper length upperPositive upperBounded lengthPositive 0
    (bEnergyDecode upper length upperPositive (highEnergyRestriction lower upper length lowerPositive upperPositive included field))
  have normSum : ‖trace‖ ^ 2 = ∑' mode, ‖trace mode‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using (lp.norm_rpow_eq_tsum (p := 2) (by norm_num) trace)
  change (∑' mode : HighAnnularMode, ENNReal.ofReal _) = ENNReal.ofReal (‖trace‖ ^ 2)
  rw [normSum,ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (lp_summable_sq trace)]
  apply tsum_congr
  intro mode
  change _ = ENNReal.ofReal (‖annularEnergyTrace upper length upperPositive upperBounded lengthPositive 0
    (bEnergyDecode upper length upperPositive (highEnergyRestriction lower upper length lowerPositive upperPositive included field)) mode‖ ^ 2)
  rw [highIncomingTrace_restricted_coefficient lower upper length lowerPositive upperPositive upperBounded lengthPositive included,
    norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,
    Real.sq_sqrt (zero_le_one.trans (annularFrequency_one_le _ _))]

end Grad.AnnularIncomingIntegrability
