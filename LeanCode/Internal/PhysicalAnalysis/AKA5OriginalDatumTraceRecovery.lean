import AKA4SameResponseBoundaryRecovery

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularForwardTraces
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCurrentBoundary Grad.AnnularLowEnergy Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularCrossMaps
open Grad.ActualBoundaryPrimitives Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularSourceGraph Grad.AnnularCurrentSource Grad.AnnularPhysicalSolution
open Grad.AnnularTiltedReference Grad.GaugeCoefficients.Physical.Allocation
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule traceCoupledRealNormed traceCoupledRealModule

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)

theorem originalSharedResponse_weighted (data : OriginalStrongCarrier parameters lower 0 0) :
    originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive
      (originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) =
      sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
        (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data) :=
  (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive).apply_symm_apply _

private theorem weightedOriginalData_graphPair (data : OriginalStrongCarrier parameters lower 0 0) :
    (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data).val.ofLp.1.ofLp.2.ofLp.1 =
      data.val.ofLp.1.ofLp.1 :=
  congrArg (fun original : OriginalStrongCarrier parameters lower 0 0 => original.val.ofLp.1.ofLp.1)
    ((originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0).symm_apply_apply data)

private theorem weightedOriginalData_outer (data : OriginalStrongCarrier parameters lower 0 0) :
    (strongHighGraphData parameters lower positive (lowerHalf.trans (by norm_num))
      (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)).datum =
      data.val.ofLp.2.ofLp.1 :=
  congrArg (fun original : OriginalStrongCarrier parameters lower 0 0 => original.val.ofLp.2.ofLp.1)
    ((originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0).symm_apply_apply data)

private theorem weightedOriginalData_low (data : OriginalStrongCarrier parameters lower 0 0) :
    originalLowIncomingUnweightMap parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
        (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)).ofLp.2 =
      data.val.ofLp.2.ofLp.2.ofLp.2 :=
  congrArg (fun original : OriginalStrongCarrier parameters lower 0 0 => original.val.ofLp.2.ofLp.2.ofLp.2)
    ((originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0).symm_apply_apply data)

/-- The full outer forward trace recovers the independently prescribed
original h of the SAME inverse response. -/
theorem originalOuterBoundaryTrace_response (data : OriginalStrongCarrier parameters lower 0 0) :
    originalOuterBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state
      (originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data,
        data.val.ofLp.1.ofLp.1) = data.val.ofLp.2.ofLp.1 := by
  let strong := originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data
  let response := sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small strong
  have weighted := originalSharedResponse_weighted parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  have source := weightedOriginalData_graphPair parameters length lower positive lowerHalf lengthPositive data
  have outer := weightedOriginalData_outer parameters length lower positive lowerHalf lengthPositive data
  calc
    _ = coupledFullOuterBoundary parameters length compact lower positive lowerHalf lengthPositive state
        (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive
          (originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data))
        data.val.ofLp.1.ofLp.1 :=
      originalOuterBoundaryTrace_to_coupled parameters length compact lower positive lowerHalf lengthPositive state _ _
    _ = coupledFullOuterBoundary parameters length compact lower positive lowerHalf lengthPositive state response
        data.val.ofLp.1.ofLp.1 := congrArg
      (fun field => coupledFullOuterBoundary parameters length compact lower positive lowerHalf lengthPositive state field data.val.ofLp.1.ofLp.1) weighted
    _ = coupledFullOuterBoundary parameters length compact lower positive lowerHalf lengthPositive state response
        strong.val.ofLp.1.ofLp.2.ofLp.1 := congrArg
      (coupledFullOuterBoundary parameters length compact lower positive lowerHalf lengthPositive state response) source.symm
    _ = data.val.ofLp.2.ofLp.1 :=
      (sharedStrongResponse_coupledFullOuter parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small strong).trans outer


/-- The exact original high incoming norm is restored, including its
literal inverse power of the accepted 9/4 tilt. -/
theorem originalHighIncomingTrace_response (data : OriginalStrongCarrier parameters lower 0 0) :
    originalHighIncomingTrace parameters lower length positive lowerHalf lengthPositive
      (originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) =
      data.val.ofLp.2.ofLp.2.ofLp.1 := by
  change lower ^ (9 / 4 : ℝ) •
    annularEnergyTrace lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (bEnergyDecode lower length positive
        (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive
          (originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)).ofLp.1.ofLp.1) = _
  rw [originalSharedResponse_weighted,sharedStrongResponse_highIncoming,originalStrongWeightEquivalence_eq_reconstruction]
  change lower ^ (9 / 4 : ℝ) • (lower ^ (-9 / 4 : ℝ) • data.val.ofLp.2.ofLp.2.ofLp.1) = _
  rw [smul_smul,← Real.rpow_add positive]
  norm_num

/-- Both low incoming d/Rk coordinates are recovered by the actual
BF5 normalization inverse, with no low angular mode discarded. -/
theorem originalLowIncomingTrace_response (data : OriginalStrongCarrier parameters lower 0 0) :
    originalLowIncomingTrace parameters lower length positive lowerHalf lengthPositive
      (originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) =
      data.val.ofLp.2.ofLp.2.ofLp.2 := by
  change originalLowIncomingUnweightMap parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive
    (lowIncomingTrace lower length positive (lowerHalf.trans_lt (by norm_num))
      (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive
        (originalSharedResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)).ofLp.2) = _
  rw [originalSharedResponse_weighted,sharedStrongResponse_lowIncoming]
  exact weightedOriginalData_low parameters length lower positive lowerHalf lengthPositive data

end Grad.AnnularForwardTraces
