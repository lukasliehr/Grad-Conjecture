import AKG25GenuineHighPhysicalConverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularRestriction
open Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularVariational Grad.AnnularCurrentSource Grad.AnnularLowEnergy Grad.AnnularReconstruction
open Grad.AnnularCoupledInverse Grad.AnnularCrossMaps Grad.AnnularForwardTraces Grad.AnnularSourceGraph
open Grad.AnnularTiltedReference Grad.AnnularCurrentEnergy Grad.AnnularCurrentGreen Grad.AnnularCurrentSolution
open Grad.AnnularPhysicalSolution Grad.AnnularFullSource Grad.AnnularCurrentBoundary Grad.AnnularCurrentLow Grad.AnnularKnownLow
open Grad.GaugeCoefficients.Physical.Allocation

private theorem boundaryMoveLow {E : Type*} [AddCommGroup E] (high low datum : E)
    (equation : high + low = datum) : high = datum + -low := by
  rw [← equation]
  abel

private theorem subtractDiagonal {E : Type*} [AddCommGroup E] (diagonal known cross : E) :
    diagonal + known + cross - diagonal = known + cross := by abel

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact)

include small

/-- Full physical weak rows plus actual traces recover the original coupled
variational equation. The derivative coordinates belong to the genuine graphs. -/
theorem strongCoupledEquation_of_fullPhysical
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (candidate : CoupledSpace lower length positive lengthPositive)
    (output : strongCandidateHighOutput parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state data candidate =
      fullStrongHighPacket parameters length compact lower positive lowerHalf lengthPositive state data candidate)
    (compactEquation : CompactPhysicalPacketEquation parameters lower length positive lengthPositive widthHalf widthLength
      (fullStrongHighPacket parameters length compact lower positive lowerHalf lengthPositive state data candidate))
    (lowRow : candidate.ofLp.2.val 1 = strongLowPhysicalRHS parameters length compact lower positive
      (lowerHalf.trans (by norm_num)) lengthPositive state data candidate)
    (highIncoming : annularEnergyTrace lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (bEnergyDecode lower length positive candidate.ofLp.1.ofLp.1) =
      (strongHighGraphData parameters lower positive (lowerHalf.trans (by norm_num)) data).innerValue)
    (lowIncoming : lowIncomingTrace lower length positive (lowerHalf.trans_lt (by norm_num)) candidate.ofLp.2 =
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.2)
    (outer : coupledFullOuterBoundary parameters length compact lower positive lowerHalf lengthPositive state candidate data.val.ofLp.1.ofLp.2.ofLp.1 =
      (strongHighGraphData parameters lower positive (lowerHalf.trans (by norm_num)) data).datum) :
    StrongCoupledEquation parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state data candidate := by
  let corrected := strongCorrectedHighData parameters length compact lower positive lowerHalf lengthPositive state data candidate.ofLp.2
  have actualCompact := (congrArg (CompactPhysicalPacketEquation parameters lower length positive lengthPositive widthHalf widthLength) output).mpr compactEquation
  have actualValue := (fullStrongHighPacket_fluxValue parameters length compact lower positive lowerHalf lengthPositive state data candidate).trans
    (congrArg (highPhysicalOutput lower 0) output.symm)
  have boundary : graphNativePhysicalBoundary state.outerInverseState 0 0
      (coupledHighFluxOuter parameters lower length positive lowerHalf lengthPositive candidate)
      (actualCurrentHighOuterTrace parameters lower length positive lowerHalf lengthPositive 0 0 candidate.ofLp.1.ofLp.1)
      (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 corrected.graphs) = corrected.datum :=
    boundaryMoveLow _ _ _ outer
  refine ⟨highSourceEquation_of_actualCompact parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (coupledPrimitive_highSmall parameters length compact state small) corrected candidate highIncoming actualCompact actualValue boundary,?_⟩
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ (LowEnergyBulk lower) LowEnergyBoundary).injective
  apply Prod.ext
  · change candidate.ofLp.2.val 1 - lowCurrentBulk parameters length compact lower lengthPositive positive (lowerHalf.trans (by norm_num)) state
      (candidate.ofLp.2.val 0) = knownLowForcing parameters length compact lower positive (lowerHalf.trans (by norm_num)) state
        (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data)
        (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2 +
      highToLowBulkCross parameters lower length compact lengthPositive positive (lowerHalf.trans (by norm_num)) state candidate.ofLp.1
    exact (congrArg (fun value => value - lowCurrentBulk parameters length compact lower lengthPositive positive (lowerHalf.trans (by norm_num)) state
      (candidate.ofLp.2.val 0)) (lowRow.trans
        (strongLowPhysicalRHS_decomposition parameters length compact lower positive (lowerHalf.trans (by norm_num)) lengthPositive state data candidate))).trans
          (subtractDiagonal _ _ _)
  · change lowIncomingTrace lower length positive (lowerHalf.trans_lt (by norm_num)) candidate.ofLp.2 =
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.2 + 0
    simpa only [add_zero] using lowIncoming

/-- The genuine full converse in ORIGINAL BF5/BF6 coordinates. The boundary
premise is the explicit bounded trace of the same candidate and copied graphs. -/
theorem originalStrongEquation_of_fullPhysical
    (data : OriginalStrongCarrier parameters lower 0 0) (candidate : OriginalCoupledSpace lower length positive)
    (output : strongCandidateHighOutput parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)
      (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate) =
      fullStrongHighPacket parameters length compact lower positive lowerHalf lengthPositive state
        (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)
        (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate))
    (compactEquation : CompactPhysicalPacketEquation parameters lower length positive lengthPositive widthHalf widthLength
      (fullStrongHighPacket parameters length compact lower positive lowerHalf lengthPositive state
        (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)
        (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate)))
    (lowRow : (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate).ofLp.2.val 1 =
      strongLowPhysicalRHS parameters length compact lower positive (lowerHalf.trans (by norm_num)) lengthPositive state
        (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)
        (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate))
    (boundary : originalBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state
      (candidate,data.val.ofLp.1.ofLp.1) = data.val.ofLp.2) :
    OriginalStrongCoupledEquation parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state data candidate :=
  strongCoupledEquation_of_fullPhysical parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small _ _
    output compactEquation lowRow
    (originalBoundaryTrace_highIncoming parameters length lower positive lowerHalf lengthPositive compact state data candidate boundary)
    (originalBoundaryTrace_lowIncoming parameters length lower positive lowerHalf lengthPositive compact state data candidate boundary)
    (originalBoundaryTrace_fullOuter parameters length lower positive lowerHalf lengthPositive compact state data candidate boundary)

end Grad.AnnularRestriction
