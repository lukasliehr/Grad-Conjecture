import AKI33ArbitraryHighOutputFidelity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
open Set Filter MeasureTheory
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularFullGraph
open Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.AnnularHighRadial
open Grad.AnnularCurrentLow Grad.AnnularCurrentSource Grad.AnnularCurrentEnergy Grad.AnnularLowEnergy
open Grad.AnnularVariational Grad.CircularHighRegularity Grad.BoundaryKernelAction Grad.AnnularCurrentGreen
open Grad.AnnularRestriction Grad.AnnularPhysicalSolution
open Grad.GaugeCoefficients.Physical.WeightedTrace

private theorem highFluxRaw_normalize (length radius : ℝ) (mode : ℤ × ℤ) (x c v g : ComplexEuclidean 1) :
    -((radius : ℂ)⁻¹ • x) - (Complex.I * (((mode.2 : ℝ) / length) : ℝ)) • c -
      (Complex.I * (mode.1 : ℂ)) • ((radius : ℂ)⁻¹ • v) + (Complex.I * (mode.1 : ℂ)) • g =
    (-((radius : ℂ)⁻¹)) • x - (length : ℂ)⁻¹ • (frequencyNumerator (some true) mode • c) -
      (radius : ℂ)⁻¹ • (frequencyNumerator (some false) mode • v) + frequencyNumerator (some false) mode • g := by
  ext slot
  simp only [frequencyNumerator,PiLp.add_apply,PiLp.sub_apply,PiLp.neg_apply,PiLp.smul_apply,smul_eq_mul]
  push_cast
  simp only [div_eq_mul_inv]
  ring

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (data : OriginalStrongCarrier parameters lower 0 0) (candidate : OriginalCoupledSpace lower length positive)
    (tuple : OriginalSmoothTuple parameters lower)
    (represented : OriginalTupleObservation parameters length compact lower positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive state tuple
      (originalFiveBlockObservation parameters lower length positive (data,candidate)))

private abbrev fluxCandidate := originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate
private abbrev fluxDatum := originalToStrong parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data
private abbrev fluxPacket := fullStrongHighPacket parameters length compact lower positive lowerHalf lengthPositive state
  (fluxDatum parameters length lower positive lowerHalf lengthPositive data)
  (fluxCandidate parameters length lower positive lowerHalf lengthPositive candidate)

include represented

/-- The arbitrary tuple's AH24 G3 is the genuine raw flux derivative of the
SAME full high packet, including the original positive Rg contribution. -/
theorem OriginalTupleObservation.highFluxRHS (mode : HighAnnularMode) :
    rawHighXPacketRHS parameters lower length positive
      (fluxPacket parameters length compact lower positive lowerHalf lengthPositive state data candidate) mode =ᵐ[volume.restrict (Icc lower 1)]
      fun radius => frequencyNumerator (some false) mode.val •
        originalTupleSlopeCurve parameters lower (lowerHalf.trans_lt (by norm_num)) tuple 0 mode.val radius := by
  let field := fluxCandidate parameters length lower positive lowerHalf lengthPositive candidate
  let datum := fluxDatum parameters length lower positive lowerHalf lengthPositive data
  let row := fun index => lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state index
    (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) datum field)
  let x := highBulkIntoFull lower (field.ofLp.1.ofLp.2.val 0)
  let g := (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 datum).ofLp.1.ofLp.2
  have literal : rawHighXPacketRHS parameters lower length positive
      (fluxPacket parameters length compact lower positive lowerHalf lengthPositive state data candidate) mode =
      collarScalar 1 lower (rawHighPhase parameters lower positive mode.val.2)
        (-collarScalar 1 lower (highReciprocalRadius lower positive) (radialOrdinary 1 lower positive (x mode.val)) -
          (Complex.I * (((mode.val.2 : ℝ) / length) : ℝ)) • radialOrdinary 1 lower positive (row 1 mode.val) -
          (Complex.I * (mode.val.1 : ℂ)) • collarScalar 1 lower (highReciprocalRadius lower positive)
            (radialOrdinary 1 lower positive (row 2 mode.val)) +
          (Complex.I * (mode.val.1 : ℂ)) • radialOrdinary 1 lower positive (g mode.val)) := by
    rw [rawHighXPacketRHS_full_sources]
    have same := fullStrongHighPacket_fluxValue parameters length compact lower positive lowerHalf lengthPositive state datum field
    have sameMode := congrArg (fun value : AnnularBulk lower => value mode) same
    have xMode : x mode.val = field.ofLp.1.ofLp.2.val 0 mode := highBulkIntoFull_high lower _ mode
    exact congrArg (fun storedX : RadialL2 1 lower =>
      collarScalar 1 lower (rawHighPhase parameters lower positive mode.val.2)
        (-collarScalar 1 lower (highReciprocalRadius lower positive) (radialOrdinary 1 lower positive storedX) -
          (Complex.I * (((mode.val.2 : ℝ) / length) : ℝ)) • radialOrdinary 1 lower positive (row 1 mode.val) -
          (Complex.I * (mode.val.1 : ℂ)) • collarScalar 1 lower (highReciprocalRadius lower positive)
            (radialOrdinary 1 lower positive (row 2 mode.val)) +
          (Complex.I * (mode.val.1 : ℂ)) • radialOrdinary 1 lower positive (g mode.val)))
      (sameMode.symm.trans xMode.symm)
  rw [literal]
  filter_upwards [rawHighFlux_full_decode parameters length lower positive x (row 1) (row 2) g mode.val,
    sameCoupledXCoefficient_high_stored parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive field mode,
    represented.rawFlux parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state data candidate tuple,
    ae_restrict_mem measurableSet_Icc] with radius decoded sameX original inside
  rw [decoded,highFluxRaw_normalize,sameX,radialClamp_eq lower (lowerHalf.trans (by norm_num)) radius inside,
    originalTupleSlopeCurve_same parameters lower (lowerHalf.trans_lt (by norm_num)) tuple 0 mode.val radius inside,
    original inside mode.val]
  rfl

end Grad.AnnularOriginalSmoothCore
