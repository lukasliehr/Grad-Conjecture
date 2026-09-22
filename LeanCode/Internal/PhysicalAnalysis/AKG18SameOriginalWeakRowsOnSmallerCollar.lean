import AKG17FullHighPhysicalPacketRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularRestriction
open Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularForwardDatum Grad.AnnularVariational Grad.AnnularCurrentGreen Grad.AnnularCurrentEnergy
open Grad.AnnularCurrentSource Grad.AnnularKnownLow Grad.AnnularCurrentLow Grad.AnnularLowEnergy
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularCrossMaps
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact lower upper : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperHalf : upper ≤ 1 / 2)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (data : OriginalStrongCarrier parameters lower 0 0) (target : OriginalStrongCarrier parameters upper 0 0)
    (sameSources : target.val.ofLp.1 = originalFullSourceRestriction parameters lower upper included data.val.ofLp.1)
    (candidate : OriginalCoupledSpace lower length lowerPositive)
    (equation : OriginalStrongCoupledEquation parameters length compact lower lowerPositive (included.trans upperHalf)
      lengthPositive widthHalf widthLength state data candidate)
include small sameSources equation

/-- The actual original full high compact flux PDE survives passage to the
smaller collar, including the copied source c/rV rows and positive Rg. -/
theorem originalRestrictedCandidate_fullCompact :
    CompactPhysicalPacketEquation parameters upper length upperPositive lengthPositive widthHalf widthLength
      (fullStrongHighPacket parameters length compact upper upperPositive upperHalf lengthPositive state
        (originalStrongWeightEquivalence parameters upper length upperPositive (upperHalf.trans (by norm_num)) lengthPositive 0 0 target)
        (originalCoupledEquivalence parameters upper length upperPositive (upperHalf.trans (by norm_num)) lengthPositive
          (originalRetainedRestriction parameters lower upper length lowerPositive upperPositive
            (upperHalf.trans_lt (by norm_num)) lengthPositive included candidate))) := by
  let sourceData := originalStrongWeightEquivalence parameters lower length lowerPositive
    ((included.trans upperHalf).trans (by norm_num)) lengthPositive 0 0 data
  let sourceCandidate := originalCoupledEquivalence parameters lower length lowerPositive
    ((included.trans upperHalf).trans (by norm_num)) lengthPositive candidate
  have same : sourceCandidate = sharedStrongResponse parameters length compact lower lowerPositive (included.trans upperHalf)
      lengthPositive widthHalf widthLength state small sourceData :=
    sharedStrongResponse_unique parameters length compact lower lowerPositive (included.trans upperHalf)
      lengthPositive widthHalf widthLength state small sourceData sourceCandidate equation
  have sourceCompact := (congrArg (fun value : CoupledSpace lower length lowerPositive lengthPositive =>
    CompactPhysicalPacketEquation parameters lower length lowerPositive lengthPositive widthHalf widthLength
      (fullStrongHighPacket parameters length compact lower lowerPositive (included.trans upperHalf) lengthPositive state sourceData value)) same).mpr
        (sharedStrongResponse_fullCompact parameters length compact lower lowerPositive (included.trans upperHalf)
          lengthPositive widthHalf widthLength state small sourceData)
  have restricted := compactPhysicalPacketEquation_restriction lower upper included lowerPositive upperPositive parameters length
    (upperHalf.trans_lt (by norm_num)) lengthPositive widthHalf widthLength _ sourceCompact
  exact (congrArg (CompactPhysicalPacketEquation parameters upper length upperPositive lengthPositive widthHalf widthLength)
    (originalFullStrongHighPacket_restriction parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state data target sameSources candidate)).mp restricted

/-- The actual stored derivative coordinate of the original low graph
satisfies the SAME full physical equation after restriction. -/
theorem originalRestrictedCandidate_fullLowRow :
    let restricted := originalCoupledEquivalence parameters upper length upperPositive (upperHalf.trans (by norm_num)) lengthPositive
      (originalRetainedRestriction parameters lower upper length lowerPositive upperPositive
        (upperHalf.trans_lt (by norm_num)) lengthPositive included candidate)
    restricted.ofLp.2.val 1 = strongLowPhysicalRHS parameters length compact upper upperPositive
      (upperHalf.trans (by norm_num)) lengthPositive state
      (originalStrongWeightEquivalence parameters upper length upperPositive (upperHalf.trans (by norm_num)) lengthPositive 0 0 target) restricted := by
  dsimp only
  let sourceData := originalStrongWeightEquivalence parameters lower length lowerPositive
    ((included.trans upperHalf).trans (by norm_num)) lengthPositive 0 0 data
  let sourceCandidate := originalCoupledEquivalence parameters lower length lowerPositive
    ((included.trans upperHalf).trans (by norm_num)) lengthPositive candidate
  have same : sourceCandidate = sharedStrongResponse parameters length compact lower lowerPositive (included.trans upperHalf)
      lengthPositive widthHalf widthLength state small sourceData :=
    sharedStrongResponse_unique parameters length compact lower lowerPositive (included.trans upperHalf)
      lengthPositive widthHalf widthLength state small sourceData sourceCandidate equation
  have sourceRow : sourceCandidate.ofLp.2.val 1 = strongLowPhysicalRHS parameters length compact lower lowerPositive
      ((included.trans upperHalf).trans (by norm_num)) lengthPositive state sourceData sourceCandidate :=
    (congrArg (fun value : CoupledSpace lower length lowerPositive lengthPositive => value.ofLp.2.val 1) same).trans
      ((sharedStrongResponse_fullLowRow parameters length compact lower lowerPositive lengthPositive state
        (included.trans upperHalf) widthHalf widthLength small sourceData).trans
          (congrArg (strongLowPhysicalRHS parameters length compact lower lowerPositive
            ((included.trans upperHalf).trans (by norm_num)) lengthPositive state sourceData) same.symm))
  have restrictedSlope := congrArg (fun value : CoupledSpace upper length upperPositive lengthPositive => value.ofLp.2.val 1)
    (originalRetainedRestriction_weighted parameters lower upper length lowerPositive upperPositive
      (upperHalf.trans_lt (by norm_num)) lengthPositive included candidate)
  exact restrictedSlope.trans
    ((congrArg (collarBulkRestriction LowAnnularIndex 1 lower upper included) sourceRow).trans
      (originalStrongLowPhysicalRHS_restriction parameters length compact lower upper lowerPositive upperPositive
        (upperHalf.trans_lt (by norm_num)) lengthPositive included state data target sameSources candidate))

end Grad.AnnularRestriction
