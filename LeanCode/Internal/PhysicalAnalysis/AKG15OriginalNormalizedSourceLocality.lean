import AKG14GenuineCompactFluxLocality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularRestriction
open Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularForwardDatum Grad.AnnularVariational Grad.AnnularCurrentGreen Grad.AnnularCurrentEnergy
open Grad.AnnularCurrentSource Grad.AnnularKnownLow

variable (parameters : PhaseParameters) (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (bounded : upper ≤ 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (data : OriginalStrongCarrier parameters lower 0 0) (target : OriginalStrongCarrier parameters upper 0 0)
    (sameSources : target.val.ofLp.1 = originalFullSourceRestriction parameters lower upper included data.val.ofLp.1)

include sameSources

theorem originalStrongWeight_knownRows_restriction (slot : Fin 4) :
    strongKnownBulk parameters upper upperPositive bounded
      (originalStrongWeightEquivalence parameters upper length upperPositive bounded lengthPositive 0 0 target) slot =
    originalBulkRestriction 1 lower upper included
      (strongKnownBulk parameters lower lowerPositive (included.trans bounded)
        (originalStrongWeightEquivalence parameters lower length lowerPositive (included.trans bounded) lengthPositive 0 0 data) slot) := by
  exact (congrArg (fun rows : HighKnownSourceBulk upper => rows slot)
    (originalStrongWeight_knownRows parameters upper length upperPositive bounded lengthPositive target)).trans
      ((congrArg (fun sources : ForwardSourceBlocks parameters upper => originalStoredKnownRows parameters upper upperPositive bounded sources slot) sameSources).trans
        ((originalStoredKnownRows_restriction parameters lower upper lowerPositive upperPositive bounded included data.val.ofLp.1 slot).trans
          (congrArg (fun rows : HighKnownSourceBulk lower => originalBulkRestriction 1 lower upper included (rows slot))
            (originalStrongWeight_knownRows parameters lower length lowerPositive (included.trans bounded) lengthPositive data).symm)))

theorem originalStrongWeight_g_restriction :
    (strongToLow parameters upper upperPositive bounded 0 0
      (originalStrongWeightEquivalence parameters upper length upperPositive bounded lengthPositive 0 0 target)).ofLp.1.ofLp.2 =
    originalBulkRestriction 1 lower upper included
      (strongToLow parameters lower lowerPositive (included.trans bounded) 0 0
        (originalStrongWeightEquivalence parameters lower length lowerPositive (included.trans bounded) lengthPositive 0 0 data)).ofLp.1.ofLp.2 := by
  have sourceG := congrArg (fun source : ForwardSourceBlocks parameters upper => source.ofLp.2.ofLp.2) sameSources
  have sameDecode := (congrArg (fun row : DivisionRow 1 upper => divisionHighWeight upper upperPositive bounded (originalAngularDecode upper row)) sourceG).trans
    ((congrArg (divisionHighWeight upper upperPositive bounded)
      (originalBulkRestriction_angularDecode lower upper included data.val.ofLp.1.ofLp.2.ofLp.2).symm).trans
        (originalBulkRestriction_highWeight lower upper included lowerPositive upperPositive bounded
          (originalAngularDecode lower data.val.ofLp.1.ofLp.2.ofLp.2)).symm)
  exact (originalStrongWeight_g parameters upper length upperPositive bounded lengthPositive target).trans
    (sameDecode.trans (congrArg (originalBulkRestriction 1 lower upper included)
      (originalStrongWeight_g parameters lower length lowerPositive (included.trans bounded) lengthPositive data).symm))

/-- The full independent f row, with no high/low projection imposed. -/
theorem originalStrongWeight_f_restriction :
    highSourceF upper (strongKnownBulk parameters upper upperPositive bounded
      (originalStrongWeightEquivalence parameters upper length upperPositive bounded lengthPositive 0 0 target)) =
    originalBulkRestriction 1 lower upper included
      (highSourceF lower (strongKnownBulk parameters lower lowerPositive (included.trans bounded)
        (originalStrongWeightEquivalence parameters lower length lowerPositive (included.trans bounded) lengthPositive 0 0 data))) :=
  originalStrongWeight_knownRows_restriction parameters lower upper length lowerPositive upperPositive bounded lengthPositive included data target sameSources 3

omit parameters lowerPositive upperPositive bounded length lengthPositive data target sameSources in
 theorem highFullRestriction_restriction (field : DivisionRow 1 lower) :
    highFullRestriction upper (originalBulkRestriction 1 lower upper included field) =
      collarBulkRestriction HighAnnularMode 1 lower upper included (highFullRestriction lower field) := by
  apply lp.ext
  funext mode
  rfl

omit parameters lowerPositive upperPositive bounded length lengthPositive data target sameSources in
 theorem highRowProjection_restriction (field : DivisionRow 1 lower) :
    originalBulkRestriction 1 lower upper included (highRowProjection lower field) =
      highRowProjection upper (originalBulkRestriction 1 lower upper included field) := by
  change originalBulkRestriction 1 lower upper included (highBulkIntoFull lower (highFullRestriction lower field)) =
    highBulkIntoFull upper (highFullRestriction upper (originalBulkRestriction 1 lower upper included field))
  rw [highBulkIntoFull_restriction,highFullRestriction_restriction]

end Grad.AnnularRestriction
