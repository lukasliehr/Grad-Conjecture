import AKG23SameRestrictedHighOutputFidelity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularVariational Grad.AnnularCurrentSource Grad.AnnularLowEnergy Grad.AnnularReconstruction
open Grad.AnnularCoupledInverse Grad.AnnularCrossMaps Grad.AnnularForwardTraces Grad.AnnularSourceGraph
open Grad.AnnularTiltedReference
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule traceCoupledRealNormed traceCoupledRealModule

variable (parameters : PhaseParameters) (length lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)

theorem originalWeighted_graphPair (data : OriginalStrongCarrier parameters lower 0 0) :
    (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data).val.ofLp.1.ofLp.2.ofLp.1 =
      data.val.ofLp.1.ofLp.1 :=
  congrArg (fun original : OriginalStrongCarrier parameters lower 0 0 => original.val.ofLp.1.ofLp.1)
    ((originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0).symm_apply_apply data)

theorem originalWeighted_outer (data : OriginalStrongCarrier parameters lower 0 0) :
    (strongHighGraphData parameters lower positive (lowerHalf.trans (by norm_num))
      (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)).datum =
      data.val.ofLp.2.ofLp.1 :=
  congrArg (fun original : OriginalStrongCarrier parameters lower 0 0 => original.val.ofLp.2.ofLp.1)
    ((originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0).symm_apply_apply data)

theorem originalWeighted_highScaled (data : OriginalStrongCarrier parameters lower 0 0) :
    lower ^ (9 / 4 : ℝ) • (strongHighGraphData parameters lower positive (lowerHalf.trans (by norm_num))
      (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)).innerValue =
      data.val.ofLp.2.ofLp.2.ofLp.1 :=
  congrArg (fun original : OriginalStrongCarrier parameters lower 0 0 => original.val.ofLp.2.ofLp.2.ofLp.1)
    ((originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0).symm_apply_apply data)

theorem originalWeighted_lowUnweight (data : OriginalStrongCarrier parameters lower 0 0) :
    originalLowIncomingUnweightMap parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
        (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)).ofLp.2 =
      data.val.ofLp.2.ofLp.2.ofLp.2 :=
  congrArg (fun original : OriginalStrongCarrier parameters lower 0 0 => original.val.ofLp.2.ofLp.2.ofLp.2)
    ((originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0).symm_apply_apply data)

variable (compact : ℝ) (state : RetainedInverseState parameters length compact)
    (data : OriginalStrongCarrier parameters lower 0 0) (candidate : OriginalCoupledSpace lower length positive)
    (boundary : originalBoundaryTrace parameters length compact lower positive lowerHalf lengthPositive state
      (candidate,data.val.ofLp.1.ofLp.1) = data.val.ofLp.2)
include boundary

theorem originalBoundaryTrace_highIncoming :
    annularEnergyTrace lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (bEnergyDecode lower length positive
        (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate).ofLp.1.ofLp.1) =
    (strongHighGraphData parameters lower positive (lowerHalf.trans (by norm_num))
      (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)).innerValue := by
  have actual := (congrArg (fun value : OriginalBoundaryCoordinates parameters => value.ofLp.2.ofLp.1) boundary).trans
    (originalWeighted_highScaled parameters length lower positive lowerHalf lengthPositive data).symm
  change lower ^ (9 / 4 : ℝ) •
    annularEnergyTrace lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (bEnergyDecode lower length positive
        (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate).ofLp.1.ofLp.1) =
    lower ^ (9 / 4 : ℝ) • (strongHighGraphData parameters lower positive (lowerHalf.trans (by norm_num))
      (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)).innerValue at actual
  have cancelled := congrArg (fun value : AnnularBoundary => lower ^ (-9 / 4 : ℝ) • value) actual
  simp only [smul_smul,← Real.rpow_add positive] at cancelled
  norm_num at cancelled
  exact cancelled

theorem originalBoundaryTrace_lowIncoming :
    lowIncomingTrace lower length positive (lowerHalf.trans_lt (by norm_num))
      (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate).ofLp.2 =
    (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0
      (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)).ofLp.2 := by
  have actual := (congrArg (fun value : OriginalBoundaryCoordinates parameters => value.ofLp.2.ofLp.2) boundary).trans
    (originalWeighted_lowUnweight parameters length lower positive lowerHalf lengthPositive data).symm
  have cancelled := congrArg (originalLowIncomingWeightMap parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive) actual
  exact (originalLowIncomingWeightMap_inverse parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive _).1.symm.trans
    (cancelled.trans (originalLowIncomingWeightMap_inverse parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive _).1)

theorem originalBoundaryTrace_fullOuter :
    coupledFullOuterBoundary parameters length compact lower positive lowerHalf lengthPositive state
      (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate)
      (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data).val.ofLp.1.ofLp.2.ofLp.1 =
    (strongHighGraphData parameters lower positive (lowerHalf.trans (by norm_num))
      (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)).datum := by
  have actual := congrArg (fun value : OriginalBoundaryCoordinates parameters => value.ofLp.1) boundary
  exact (congrArg (coupledFullOuterBoundary parameters length compact lower positive lowerHalf lengthPositive state
    (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate))
    (originalWeighted_graphPair parameters length lower positive lowerHalf lengthPositive data)).trans
      ((originalOuterBoundaryTrace_to_coupled parameters length compact lower positive lowerHalf lengthPositive state candidate data.val.ofLp.1.ofLp.1).symm.trans
        (actual.trans (originalWeighted_outer parameters length lower positive lowerHalf lengthPositive data).symm))

end Grad.AnnularRestriction
