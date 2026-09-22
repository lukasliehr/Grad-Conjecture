import AKG24OriginalBoundaryTraceNormalization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularVariational Grad.AnnularCurrentSource Grad.AnnularLowEnergy Grad.AnnularReconstruction
open Grad.AnnularCoupledInverse Grad.AnnularCrossMaps Grad.AnnularForwardTraces Grad.AnnularSourceGraph
open Grad.AnnularTiltedReference Grad.AnnularCurrentEnergy Grad.AnnularCurrentGreen Grad.AnnularCurrentSolution
open Grad.AnnularPhysicalSolution Grad.AnnularFullSource Grad.AnnularCurrentBoundary Grad.AnnularOmegaGraph Grad.AnnularFluxTrace
open Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.WeightedTrace

private theorem positiveRealComplexInverse (value : ℝ) (positive : 0 < value) (field : ComplexEuclidean 1) :
    (value : ℂ) • (value⁻¹ • field) = field := by
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) value (value⁻¹ • field)).symm.trans
    (smul_inv_smul₀ positive.ne' field)

private theorem projectFirstThree (lower : ℝ) (first second third : DivisionRow 1 lower) :
    bulkMatrixUnit lower (0 : Fin 1) (0 : Fin 3)
      (bulkMatrixUnit lower (0 : Fin 3) 0 first + bulkMatrixUnit lower (1 : Fin 3) 0 second +
        bulkMatrixUnit lower (2 : Fin 3) 0 third) = first := by
  rw [map_add,map_add,bulkScalarProjection_same,
    bulkScalarProjection_distinct lower 0 1 (by decide),bulkScalarProjection_distinct lower 0 2 (by decide),add_zero,add_zero]

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)

theorem fullStrongHighPacket_first
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (candidate : CoupledSpace lower length positive lengthPositive) :
    bulkMatrixUnit lower (0 : Fin 1) (0 : Fin 3)
      (fullStrongHighPacket parameters length compact lower positive lowerHalf lengthPositive state data candidate) =
      highBulkIntoFull lower (crossHighX lower length positive lengthPositive candidate.ofLp.1) :=
  projectFirstThree lower _ _ _

theorem fullStrongHighPacket_fluxValue
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (candidate : CoupledSpace lower length positive lengthPositive) :
    candidate.ofLp.1.ofLp.2.val 0 = highPhysicalOutput lower 0
      (fullStrongHighPacket parameters length compact lower positive lowerHalf lengthPositive state data candidate) := by
  change _ = highFullRestriction lower (bulkMatrixUnit lower (0 : Fin 1) (0 : Fin 3) _)
  rw [fullStrongHighPacket_first]
  apply lp.ext
  funext mode
  exact (highBulkIntoFull_high lower (crossHighX lower length positive lengthPositive candidate.ofLp.1) mode).symm

/-- The actual moment endpoint is forced by the SAME retained flux graph. -/
theorem physicalFluxMoment_outer_from_candidate
    (candidate : CoupledSpace lower length positive lengthPositive) (field : DivisionRow 3 lower)
    (equation : CompactPhysicalPacketEquation parameters lower length positive lengthPositive widthHalf widthLength field)
    (sameValue : candidate.ofLp.1.ofLp.2.val 0 = highPhysicalOutput lower 0 field) (mode : HighAnnularMode) :
    weightedRadialTrace 1 lower positive (lowerHalf.trans_lt (by norm_num)) 1
      (physicalFluxMomentGraph parameters lower length positive lengthPositive widthHalf widthLength
        (lowerHalf.trans_lt (by norm_num)) field equation mode) =
      (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) •
        (coupledHighFluxOuter parameters lower length positive lowerHalf lengthPositive candidate).val mode.val := by
  rw [physicalFluxMoment_outer_same parameters lower length positive (lowerHalf.trans_lt (by norm_num))
    lengthPositive widthHalf widthLength field equation candidate.ofLp.1.ofLp.2 sameValue mode,
    coupledHighFluxOuter_coefficient,annularFluxTrace_apply]
  exact (positiveRealComplexInverse _ (Real.sqrt_pos.mpr (Grad.AnnularFluxTrace.annularFrequency_pos mode)) _).symm

/-- Genuine high weak-to-variational converse on the original graph,
using the actual full output, its retained flux value and original boundary. -/
theorem highSourceEquation_of_actualCompact
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters length compact)
    (data : ActualHighGraphKnownData parameters lower 0 0)
    (candidate : CoupledSpace lower length positive lengthPositive)
    (incoming : annularEnergyTrace lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (bEnergyDecode lower length positive candidate.ofLp.1.ofLp.1) = data.innerValue)
    (equation : CompactPhysicalPacketEquation parameters lower length positive lengthPositive widthHalf widthLength
      (actualFullHighOutput parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state candidate.ofLp.1.ofLp.1 data.weighted data.auxiliary))
    (sameValue : candidate.ofLp.1.ofLp.2.val 0 = highPhysicalOutput lower 0
      (actualFullHighOutput parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state candidate.ofLp.1.ofLp.1 data.weighted data.auxiliary))
    (boundary : graphNativePhysicalBoundary state.outerInverseState 0 0
      (coupledHighFluxOuter parameters lower length positive lowerHalf lengthPositive candidate)
      (actualCurrentHighOuterTrace parameters lower length positive lowerHalf lengthPositive 0 0 candidate.ofLp.1.ofLp.1)
      (highGraphOuterTuple parameters lower positive (lowerHalf.trans_lt (by norm_num)) 0 data.graphs) = data.datum) :
    HighSourceEquation parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state data candidate.ofLp.1 := by
  have affine := (candidatePhysicalBoundary_iff parameters length compact lower positive lowerHalf lengthPositive state data candidate.ofLp.1.ofLp.1
    (coupledHighFluxOuter parameters lower length positive lowerHalf lengthPositive candidate)).mp boundary
  have outer (mode : HighAnnularMode) := (physicalFluxMoment_outer_from_candidate parameters length lower positive lowerHalf lengthPositive
    widthHalf widthLength candidate _ equation sameValue mode).trans
      (congrArg (fun value : HighBoundaryPrimitive parameters 0 0 =>
        (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) • value.val mode.val) affine)
  have same := physicalCompactCandidate_unique parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
    candidate.ofLp.1.ofLp.1 incoming equation outer
  refine ⟨incoming,?_,sameValue⟩
  intro test
  exact (congrArg (fun value : annularEnergySpace lower length positive =>
    currentHighFormValue parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state value test.val) same).trans
      ((fullKnownHighResponse_equation parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data).2.1 test)

end Grad.AnnularRestriction
