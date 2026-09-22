import AKG12LiteralLowOutputLocality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularTiltedReference Grad.AnnularCurrentSource
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem highEnergyRestriction_phase (field : annularEnergySpace lower length lowerPositive) :
    annularTiltEnergyPhase parameters upper length upperPositive lengthPositive widthHalf widthLength
      (highEnergyRestriction lower upper length lowerPositive upperPositive included field) =
    collarBulkRestriction HighAnnularMode 1 lower upper included
      (annularTiltEnergyPhase parameters lower length lowerPositive lengthPositive widthHalf widthLength field) := by
  apply lp.ext
  funext mode
  change annularTiltPhaseMap parameters upper length upperPositive lengthPositive widthHalf widthLength mode
    (annularEnergyMass upper length upperPositive (highEnergyRestriction lower upper length lowerPositive upperPositive included field) mode) = _
  rw [highEnergyRestriction_mass]
  have ratio : EqOn (annularTiltPhaseRatio parameters lower length lowerPositive mode)
      (annularTiltPhaseRatio parameters upper length upperPositive mode) (Icc upper 1) := by
    intro radius inside
    change (annularPhaseSlope parameters mode.val.2 radius - annularTiltExponent / max lower radius) /
      annularPotentialWeight lower length lowerPositive mode.val.1 mode.val.2 radius =
      (annularPhaseSlope parameters mode.val.2 radius - annularTiltExponent / max upper radius) /
        annularPotentialWeight upper length upperPositive mode.val.1 mode.val.2 radius
    rw [max_eq_right (included.trans inside.1),max_eq_right inside.1,
      annularPotentialWeight_restrict lower upper length lowerPositive upperPositive included mode.val.1 mode.val.2 inside]
  exact (scalarRadialMap_restrict lower upper included _ _ (Real.sqrt (15 / 16)) (Real.sqrt (15 / 16))
    (annularTiltPhaseRatio_bound parameters lower length lowerPositive lengthPositive widthHalf widthLength mode)
    (annularTiltPhaseRatio_bound parameters upper length upperPositive lengthPositive widthHalf widthLength mode)
    ratio (annularEnergyMass lower length lowerPositive field mode)).symm

include upperBounded in
/-- Locality of the genuine high derivative, with the original phase and
b decode. No derivative coordinate is assigned by the inverse. -/
theorem highEnergyRestriction_physicalDerivative (field : annularEnergySpace lower length lowerPositive) :
    highPhysicalDerivative parameters upper length upperPositive lengthPositive widthHalf widthLength
      (highEnergyRestriction lower upper length lowerPositive upperPositive included field) =
    collarBulkRestriction HighAnnularMode 1 lower upper included
      (highPhysicalDerivative parameters lower length lowerPositive lengthPositive widthHalf widthLength field) := by
  change annularEnergyDerivative upper length upperPositive (bEnergyDecode upper length upperPositive _)
    - annularTiltEnergyPhase parameters upper length upperPositive lengthPositive widthHalf widthLength (bEnergyDecode upper length upperPositive _) =
    collarBulkRestriction HighAnnularMode 1 lower upper included
      (annularEnergyDerivative lower length lowerPositive (bEnergyDecode lower length lowerPositive field)
        - annularTiltEnergyPhase parameters lower length lowerPositive lengthPositive widthHalf widthLength
          (bEnergyDecode lower length lowerPositive field))
  rw [← highEnergyRestriction_bDecode lower upper length lowerPositive upperPositive upperBounded included,
    highEnergyRestriction_derivative,highEnergyRestriction_phase,map_sub]

/-- Full high output projection preserves the literal modes under restriction. -/
theorem highBulkIntoFull_restriction (field : AnnularBulk lower) :
    originalBulkRestriction 1 lower upper included (highBulkIntoFull lower field) =
      highBulkIntoFull upper (collarBulkRestriction HighAnnularMode 1 lower upper included field) := by
  apply lp.ext
  funext mode
  by_cases high : 3 ≤ |mode.1|
  · change collarL2Restriction 1 lower upper included (highBulkIntoFull lower field (⟨mode,high⟩ : HighAnnularMode).val) =
      highBulkIntoFull upper (collarBulkRestriction HighAnnularMode 1 lower upper included field) (⟨mode,high⟩ : HighAnnularMode).val
    rw [highBulkIntoFull_high,highBulkIntoFull_high]
    rfl
  · change collarL2Restriction 1 lower upper included (highBulkIntoFull lower field mode) =
      highBulkIntoFull upper (collarBulkRestriction HighAnnularMode 1 lower upper included field) mode
    rw [highBulkIntoFull_low lower field mode high,highBulkIntoFull_low upper _ mode high,map_zero]

end Grad.AnnularRestriction
