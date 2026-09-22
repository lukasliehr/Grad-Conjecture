import AJC8SamePhysicalRowProjections

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
namespace Grad.AnnularStrongSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularStrongData Grad.AnnularCurrentSource Grad.AnnularCurrentEnergy Grad.AnnularCurrentGreen
open Grad.AnnularCrossMaps Grad.AnnularKnownLow Grad.AnnularLowEnergy Grad.AnnularCurrentLow
open Grad.AnnularReconstruction Grad.AnnularFullSource

theorem crossHighRestriction_same (lower : ℝ) : crossHighRestriction lower = highFullRestriction lower := by
  apply ContinuousLinearMap.ext
  intro field
  apply lp.ext
  funext mode
  rfl

def strongHighGraphData (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (data : StrongDataCarrier parameters lower positive bounded 0 0) : ActualHighGraphKnownData parameters lower 0 0 :=
  ActualHighKnownCarrier.toGraphKnownData parameters lower positive bounded 0 0
    (strongToHigh parameters lower positive bounded 0 0 data)

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (state : RetainedInverseState parameters L compact)

theorem lowCrossRow_intoFull (row : Fin 3) (field : lowEnergyGraph lower L positive) :
    highBulkIntoFull lower
      (lowToHighBulkCross parameters lower L compact lengthPositive positive (lowerHalf.trans (by norm_num)) state row field) =
    highRowProjection lower
      (lowPhysicalRowAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state row
        (lowNormalizedSevenInput parameters lower L lengthPositive positive (field.val 0))) :=
  congrArg (fun restriction : DivisionRow 1 lower →L[ℂ] AnnularBulk lower =>
    highBulkIntoFull lower (restriction
      (lowPhysicalRowAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state row
        (lowNormalizedSevenInput parameters lower L lengthPositive positive (field.val 0)))))
      (crossHighRestriction_same lower)

/-- Only the actual low field is added; the original strong source graphs
and boundary datum remain attached to the same high datum. -/
def strongCorrectedHighData
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (low : lowEnergyGraph lower L positive) : ActualHighGraphKnownData parameters lower 0 0 :=
  addCrossData parameters lower (strongHighGraphData parameters lower positive (lowerHalf.trans (by norm_num)) data)
    (lowToHighCross parameters lower L compact lengthPositive positive lowerHalf state low)

theorem strongCorrectedHighData_sourcePacket
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (low : lowEnergyGraph lower L positive) :
    knownLowSevenPacket lower (strongCorrectedHighData parameters L compact lower positive lowerHalf lengthPositive state data low).weighted =
      knownLowSevenPacket lower (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data) := by
  apply knownLowSevenPacket_same_sources lower
  · exact add_zero (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data 0)
  · exact add_zero (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data 1)
  · exact add_zero (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data 2)

theorem strongCorrectedHighData_f
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (low : lowEnergyGraph lower L positive) :
    (strongCorrectedHighData parameters L compact lower positive lowerHalf lengthPositive state data low).weighted 3 =
      highRowProjection lower
        (highSourceF lower (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data) +
          lowPhysicalRowAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 0
            (lowNormalizedSevenInput parameters lower L lengthPositive positive (low.val 0))) := by
  exact (congrArg (fun row : DivisionRow 1 lower =>
    highRowProjection lower (highSourceF lower (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data)) + row)
      (lowCrossRow_intoFull parameters L compact lower positive lowerHalf lengthPositive state 0 low)).trans (map_add _ _ _).symm

theorem strongCorrectedHighData_g
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (low : lowEnergyGraph lower L positive) :
    (strongCorrectedHighData parameters L compact lower positive lowerHalf lengthPositive state data low).auxiliary 0 =
      highRowProjection lower (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2 :=
  add_zero _

theorem strongCorrectedHighData_c
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (low : lowEnergyGraph lower L positive) :
    (strongCorrectedHighData parameters L compact lower positive lowerHalf lengthPositive state data low).auxiliary 1 =
      highRowProjection lower (lowPhysicalRowAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 1
        (lowNormalizedSevenInput parameters lower L lengthPositive positive (low.val 0))) :=
  (zero_add _).trans (lowCrossRow_intoFull parameters L compact lower positive lowerHalf lengthPositive state 1 low)

theorem strongCorrectedHighData_v
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (low : lowEnergyGraph lower L positive) :
    (strongCorrectedHighData parameters L compact lower positive lowerHalf lengthPositive state data low).auxiliary 2 =
      highRowProjection lower (lowPhysicalRowAction parameters L compact lower positive (lowerHalf.trans (by norm_num)) state 2
        (lowNormalizedSevenInput parameters lower L lengthPositive positive (low.val 0))) :=
  (zero_add _).trans (lowCrossRow_intoFull parameters L compact lower positive lowerHalf lengthPositive state 2 low)

end Grad.AnnularStrongSolution
