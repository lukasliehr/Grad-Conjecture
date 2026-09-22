import AKG22ActualFullHighOutputRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularRestriction
open Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularVariational Grad.AnnularCurrentGreen Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource
open Grad.AnnularKnownLow Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularCurrentSolution Grad.AnnularCoupledInverse Grad.AnnularCrossMaps
open Grad.GaugeCoefficients.Physical.Allocation

/-- Actual full high output on a candidate with its SAME corrected high datum. -/
def strongCandidateHighOutput (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (candidate : CoupledSpace lower length positive lengthPositive) : DivisionRow 3 lower :=
  actualFullHighOutput parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state candidate.ofLp.1.ofLp.1
    (strongCorrectedHighData parameters length compact lower positive lowerHalf lengthPositive state data candidate.ofLp.2).weighted
    (strongCorrectedHighData parameters length compact lower positive lowerHalf lengthPositive state data candidate.ofLp.2).auxiliary

theorem strongCandidateHighOutput_response (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    let solution := sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
    strongCandidateHighOutput parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state data solution =
      fullStrongHighPacket parameters length compact lower positive lowerHalf lengthPositive state data solution :=
  sharedStrongPhysicalOutput_sameFull parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data

variable (parameters : PhaseParameters) (length compact lower upper : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperHalf : upper ≤ 1 / 2)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)

theorem strongCandidateHighOutput_restriction
    (data : StrongDataCarrier parameters lower lowerPositive ((included.trans upperHalf).trans (by norm_num)) 0 0)
    (target : StrongDataCarrier parameters upper upperPositive (upperHalf.trans (by norm_num)) 0 0)
    (sameKnown : ∀ slot : Fin 4, strongKnownBulk parameters upper upperPositive (upperHalf.trans (by norm_num)) target slot =
      originalBulkRestriction 1 lower upper included
        (strongKnownBulk parameters lower lowerPositive ((included.trans upperHalf).trans (by norm_num)) data slot))
    (sameG : (strongToLow parameters upper upperPositive (upperHalf.trans (by norm_num)) 0 0 target).ofLp.1.ofLp.2 =
      originalBulkRestriction 1 lower upper included
        (strongToLow parameters lower lowerPositive ((included.trans upperHalf).trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2)
    (candidate : CoupledSpace lower length lowerPositive lengthPositive) :
    originalBulkRestriction 3 lower upper included
      (strongCandidateHighOutput parameters length compact lower lowerPositive (included.trans upperHalf) lengthPositive widthHalf widthLength state data candidate) =
    strongCandidateHighOutput parameters length compact upper upperPositive upperHalf lengthPositive widthHalf widthLength state target
      (coupledEndpointRestriction lower upper length lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) lengthPositive included candidate) := by
  have known := strongCorrectedHighData_knownRows_restriction parameters length compact lower upper lowerPositive upperPositive upperHalf
    lengthPositive included state data target sameKnown candidate.ofLp.2
  have auxiliary := strongCorrectedHighData_auxiliary_restriction parameters length compact lower upper lowerPositive upperPositive upperHalf
    lengthPositive included state data target sameG candidate.ofLp.2
  exact (actualFullHighOutput_restriction parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included
    widthHalf widthLength state candidate.ofLp.1.ofLp.1 _ _).trans
      (congrArg₂ (actualFullHighOutput parameters length compact upper upperPositive upperHalf lengthPositive widthHalf widthLength state
        (highEnergyRestriction lower upper length lowerPositive upperPositive included candidate.ofLp.1.ofLp.1)) known.symm auxiliary.symm)

/-- Exact high-output fidelity of an arbitrary original equation candidate
on the smaller collar. This is the SAME completed variable-coefficient action,
with no forward phase or smoothness assumption. -/
theorem originalRestrictedCandidate_highOutput_eq_full
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact)
    (data : OriginalStrongCarrier parameters lower 0 0) (target : OriginalStrongCarrier parameters upper 0 0)
    (sameSources : target.val.ofLp.1 = originalFullSourceRestriction parameters lower upper included data.val.ofLp.1)
    (candidate : OriginalCoupledSpace lower length lowerPositive)
    (equation : OriginalStrongCoupledEquation parameters length compact lower lowerPositive (included.trans upperHalf)
      lengthPositive widthHalf widthLength state data candidate) :
    let nextData := originalStrongWeightEquivalence parameters upper length upperPositive (upperHalf.trans (by norm_num)) lengthPositive 0 0 target
    let nextCandidate := originalCoupledEquivalence parameters upper length upperPositive (upperHalf.trans (by norm_num)) lengthPositive
      (originalRetainedRestriction parameters lower upper length lowerPositive upperPositive (upperHalf.trans_lt (by norm_num)) lengthPositive included candidate)
    strongCandidateHighOutput parameters length compact upper upperPositive upperHalf lengthPositive widthHalf widthLength state nextData nextCandidate =
      fullStrongHighPacket parameters length compact upper upperPositive upperHalf lengthPositive state nextData nextCandidate := by
  dsimp only
  let sourceData := originalStrongWeightEquivalence parameters lower length lowerPositive ((included.trans upperHalf).trans (by norm_num)) lengthPositive 0 0 data
  let sourceCandidate := originalCoupledEquivalence parameters lower length lowerPositive ((included.trans upperHalf).trans (by norm_num)) lengthPositive candidate
  have same : sourceCandidate = sharedStrongResponse parameters length compact lower lowerPositive (included.trans upperHalf)
      lengthPositive widthHalf widthLength state small sourceData :=
    sharedStrongResponse_unique parameters length compact lower lowerPositive (included.trans upperHalf) lengthPositive widthHalf widthLength state small sourceData sourceCandidate equation
  have fidelity := (congrArg (strongCandidateHighOutput parameters length compact lower lowerPositive (included.trans upperHalf)
    lengthPositive widthHalf widthLength state sourceData) same).trans
      ((strongCandidateHighOutput_response parameters length compact lower lowerPositive (included.trans upperHalf)
        lengthPositive widthHalf widthLength state small sourceData).trans
          (congrArg (fullStrongHighPacket parameters length compact lower lowerPositive (included.trans upperHalf) lengthPositive state sourceData) same.symm))
  have weighted := originalRetainedRestriction_weighted parameters lower upper length lowerPositive upperPositive
    (upperHalf.trans_lt (by norm_num)) lengthPositive included candidate
  have locality := (strongCandidateHighOutput_restriction parameters length compact lower upper lowerPositive upperPositive upperHalf
    lengthPositive included widthHalf widthLength state sourceData
    (originalStrongWeightEquivalence parameters upper length upperPositive (upperHalf.trans (by norm_num)) lengthPositive 0 0 target)
    (originalStrongWeight_knownRows_restriction parameters lower upper length lowerPositive upperPositive (upperHalf.trans (by norm_num)) lengthPositive included data target sameSources)
    (originalStrongWeight_g_restriction parameters lower upper length lowerPositive upperPositive (upperHalf.trans (by norm_num)) lengthPositive included data target sameSources)
    sourceCandidate).trans
      (congrArg (strongCandidateHighOutput parameters length compact upper upperPositive upperHalf lengthPositive widthHalf widthLength state
        (originalStrongWeightEquivalence parameters upper length upperPositive (upperHalf.trans (by norm_num)) lengthPositive 0 0 target)) weighted.symm)
  exact locality.symm.trans ((congrArg (originalBulkRestriction 3 lower upper included) fidelity).trans
    (originalFullStrongHighPacket_restriction parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state data target sameSources candidate))

end Grad.AnnularRestriction
