import AKG10OriginalCopiedSourcePacketLocality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularCurrentSource
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularForwardDatum Grad.AnnularKnownLow
open Grad.AnnularCurrentLow Grad.AnnularReconstruction Grad.AnnularCoupledInverse

/-- The literal accepted full seven input of an ORIGINAL datum/candidate
under the proved BF5/BF6 equivalences. No new physical packet is substituted. -/
def originalSevenPacket (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (data : OriginalStrongCarrier parameters lower 0 0) (candidate : OriginalCoupledSpace lower length positive) :
    DivisionRow 7 lower :=
  fullStrongSevenInput parameters length lower lengthPositive positive bounded
    (originalStrongWeightEquivalence parameters lower length positive bounded lengthPositive 0 0 data)
    (originalCoupledEquivalence parameters lower length positive bounded lengthPositive candidate)

theorem originalSevenPacket_decomposition (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (data : OriginalStrongCarrier parameters lower 0 0) (candidate : OriginalCoupledSpace lower length positive) :
    originalSevenPacket parameters lower length positive bounded lengthPositive data candidate =
      homogeneousCoupledSevenInput parameters length lower lengthPositive positive
        (originalCoupledEquivalence parameters lower length positive bounded lengthPositive candidate) +
      knownLowSevenPacket lower (originalStoredKnownRows parameters lower positive bounded data.val.ofLp.1) := by
  unfold originalSevenPacket fullStrongSevenInput
  rw [originalStrongWeight_knownRows]

theorem originalSevenPacket_restriction_of_sources (parameters : PhaseParameters) (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (data : OriginalStrongCarrier parameters lower 0 0) (target : OriginalStrongCarrier parameters upper 0 0)
    (sameSources : target.val.ofLp.1 = originalFullSourceRestriction parameters lower upper included data.val.ofLp.1)
    (candidate : OriginalCoupledSpace lower length lowerPositive) :
    originalBulkRestriction 7 lower upper included
      (originalSevenPacket parameters lower length lowerPositive (included.trans upperBounded.le) lengthPositive data candidate) =
    originalSevenPacket parameters upper length upperPositive upperBounded.le lengthPositive target
      (originalRetainedRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included candidate) := by
  have sameKnown : originalStoredKnownRows parameters upper upperPositive upperBounded.le target.val.ofLp.1 =
      knownRowsRestriction lower upper included
        (originalStoredKnownRows parameters lower lowerPositive (included.trans upperBounded.le) data.val.ofLp.1) := by
    rw [sameSources]
    apply PiLp.ext
    intro slot
    exact originalStoredKnownRows_restriction parameters lower upper lowerPositive upperPositive upperBounded.le included data.val.ofLp.1 slot
  have homogeneous := (homogeneousCoupledSevenInput_restriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included
    (originalCoupledEquivalence parameters lower length lowerPositive (included.trans upperBounded.le) lengthPositive candidate)).trans
      (congrArg (homogeneousCoupledSevenInput parameters length upper lengthPositive upperPositive)
        (originalRetainedRestriction_weighted parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included candidate).symm)
  have known := (knownLowSevenPacket_restriction lower upper included
    (originalStoredKnownRows parameters lower lowerPositive (included.trans upperBounded.le) data.val.ofLp.1)).trans
      (congrArg (knownLowSevenPacket upper) sameKnown.symm)
  exact (congrArg (originalBulkRestriction 7 lower upper included)
    (originalSevenPacket_decomposition parameters lower length lowerPositive (included.trans upperBounded.le) lengthPositive data candidate)).trans
      ((map_add (originalBulkRestriction 7 lower upper included) _ _).trans
        ((congrArg₂ (fun a b : DivisionRow 7 upper => a + b) homogeneous known).trans
          (originalSevenPacket_decomposition parameters upper length upperPositive upperBounded.le lengthPositive target _).symm))

variable (parameters : PhaseParameters) (length compact lower upper : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperHalf : upper ≤ 1 / 2)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (state : RetainedInverseState parameters length compact)

theorem originalSevenPacket_endpointDatum (data : OriginalStrongCarrier parameters lower 0 0)
    (candidate : OriginalCoupledSpace lower length lowerPositive) :
    originalBulkRestriction 7 lower upper included
      (originalSevenPacket parameters lower length lowerPositive ((included.trans upperHalf).trans (by norm_num)) lengthPositive data candidate) =
    originalSevenPacket parameters upper length upperPositive (upperHalf.trans (by norm_num)) lengthPositive
      (originalEndpointDatum parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state
        (Grad.AnnularForwardDatum.originalFiveBlockObservation parameters lower length lowerPositive data candidate))
      (originalRetainedRestriction parameters lower upper length lowerPositive upperPositive
        (upperHalf.trans_lt (by norm_num)) lengthPositive included candidate) :=
  originalSevenPacket_restriction_of_sources parameters lower upper length lowerPositive upperPositive
    (upperHalf.trans_lt (by norm_num)) lengthPositive included data _
    (originalEndpointDatum_sources parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state data candidate) candidate

/-- Every actual full physical j/c/rV row is local, with the rebuilt datum
providing the SAME copied sources once and the SAME original kernel family. -/
theorem originalFullPhysicalRow_endpointDatum (data : OriginalStrongCarrier parameters lower 0 0)
    (candidate : OriginalCoupledSpace lower length lowerPositive) (row : Fin 3) :
    originalBulkRestriction 1 lower upper included
      (lowPhysicalRowAction parameters length compact lower lowerPositive ((included.trans upperHalf).trans (by norm_num)) state row
        (originalSevenPacket parameters lower length lowerPositive ((included.trans upperHalf).trans (by norm_num)) lengthPositive data candidate)) =
    lowPhysicalRowAction parameters length compact upper upperPositive (upperHalf.trans (by norm_num)) state row
      (originalSevenPacket parameters upper length upperPositive (upperHalf.trans (by norm_num)) lengthPositive
        (originalEndpointDatum parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state
          (Grad.AnnularForwardDatum.originalFiveBlockObservation parameters lower length lowerPositive data candidate))
        (originalRetainedRestriction parameters lower upper length lowerPositive upperPositive
          (upperHalf.trans_lt (by norm_num)) lengthPositive included candidate)) := by
  exact (originalBulkRestriction_regularRadialBulkAction parameters 0 lower upper included lowerPositive upperPositive
    (upperHalf.trans (by norm_num)) (lowPhysicalRowKernel parameters length compact state row)
    (lowPhysicalRowKernel_regular parameters length compact state row)
    (originalSevenPacket parameters lower length lowerPositive ((included.trans upperHalf).trans (by norm_num)) lengthPositive data candidate)).trans
      (congrArg (lowPhysicalRowAction parameters length compact upper upperPositive (upperHalf.trans (by norm_num)) state row)
        (originalSevenPacket_endpointDatum parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state data candidate))

end Grad.AnnularRestriction
