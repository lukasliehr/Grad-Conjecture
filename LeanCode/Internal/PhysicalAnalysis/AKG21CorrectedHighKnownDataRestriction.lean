import AKG20SameLowOnlyPacketRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularRestriction
open Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularVariational Grad.AnnularCurrentGreen Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource
open Grad.AnnularKnownLow Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.AnnularReconstruction

private theorem correctedHigh_sources (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (field : lowEnergyGraph lower length positive) (slot : Fin 4) (source : slot.val < 3) :
    (strongCorrectedHighData parameters length compact lower positive lowerHalf lengthPositive state data field).weighted slot =
      strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data slot := by
  fin_cases slot
  · exact add_zero _
  · exact add_zero _
  · exact add_zero _
  · norm_num at source

/-- The corrected high datum uses the same copied sources and the actual
restricted low first row. In particular the independent f is retained. -/
theorem strongCorrectedHighData_knownRows_restriction (parameters : PhaseParameters) (length compact lower upper : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperHalf : upper ≤ 1 / 2)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (state : RetainedInverseState parameters length compact)
    (data : StrongDataCarrier parameters lower lowerPositive ((included.trans upperHalf).trans (by norm_num)) 0 0)
    (target : StrongDataCarrier parameters upper upperPositive (upperHalf.trans (by norm_num)) 0 0)
    (sameKnown : ∀ slot : Fin 4, strongKnownBulk parameters upper upperPositive (upperHalf.trans (by norm_num)) target slot =
      originalBulkRestriction 1 lower upper included
        (strongKnownBulk parameters lower lowerPositive ((included.trans upperHalf).trans (by norm_num)) data slot))
    (field : lowEnergyGraph lower length lowerPositive) :
    (strongCorrectedHighData parameters length compact upper upperPositive upperHalf lengthPositive state target
      (lowEnergyRestriction lower upper length included lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) field)).weighted =
    knownRowsRestriction lower upper included
      (strongCorrectedHighData parameters length compact lower lowerPositive (included.trans upperHalf) lengthPositive state data field).weighted := by
  apply PiLp.ext
  intro slot
  change _ = originalBulkRestriction 1 lower upper included
    ((strongCorrectedHighData parameters length compact lower lowerPositive (included.trans upperHalf) lengthPositive state data field).weighted slot)
  by_cases source : slot.val < 3
  · rw [correctedHigh_sources parameters length compact upper upperPositive upperHalf lengthPositive state target _ slot source,
      correctedHigh_sources parameters length compact lower lowerPositive (included.trans upperHalf) lengthPositive state data field slot source]
    exact sameKnown slot
  · have slotThree : slot = 3 := by apply Fin.ext; omega
    subst slot
    have row := originalBulkRestriction_regularRadialBulkAction parameters 0 lower upper included lowerPositive upperPositive
      (upperHalf.trans (by norm_num)) (lowPhysicalRowKernel parameters length compact state 0)
      (lowPhysicalRowKernel_regular parameters length compact state 0)
      (lowNormalizedSevenInput parameters lower length lengthPositive lowerPositive (field.val 0))
    have packet := lowNormalizedSevenInput_restriction parameters lower upper length lowerPositive upperPositive
      (upperHalf.trans_lt (by norm_num)) lengthPositive included field
    have sameRow := row.trans (congrArg (lowPhysicalRowAction parameters length compact upper upperPositive
      (upperHalf.trans (by norm_num)) state 0) packet)
    have combined := (map_add (originalBulkRestriction 1 lower upper included)
      (highSourceF lower (strongKnownBulk parameters lower lowerPositive ((included.trans upperHalf).trans (by norm_num)) data))
      (lowPhysicalRowAction parameters length compact lower lowerPositive ((included.trans upperHalf).trans (by norm_num)) state 0
        (lowNormalizedSevenInput parameters lower length lengthPositive lowerPositive (field.val 0)))).trans
      (congrArg₂ (fun a b : DivisionRow 1 upper => a + b) (sameKnown 3).symm sameRow)
    have projected := (highRowProjection_restriction lower upper included _).trans (congrArg (highRowProjection upper) combined)
    exact (strongCorrectedHighData_f parameters length compact upper upperPositive upperHalf lengthPositive state target _).trans
      (projected.symm.trans (congrArg (originalBulkRestriction 1 lower upper included)
        (strongCorrectedHighData_f parameters length compact lower lowerPositive (included.trans upperHalf) lengthPositive state data field).symm))

end Grad.AnnularRestriction
