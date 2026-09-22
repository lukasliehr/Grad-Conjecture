import AKV8GeneralHighFirstRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
open Set Filter MeasureTheory
namespace Grad.AnnularGeneralSourceRegularity
open Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularHighRadial Grad.AnnularCurrentLow Grad.AnnularReconstruction Grad.CircularHighRegularity
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularSmoothSources Grad.AnnularStrongOrbit Grad.AnnularCurrentSource Grad.AnnularCurrentEnergy
open Grad.AnnularCurrentGreen Grad.AnnularPhysicalSolution Grad.AnnularVariational Grad.AnnularSourceGraph
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)

private theorem generalHighFlux_source_split (length radius : ℝ) (mode : ℤ × ℤ)
    (x j c v sourceJ sourceC sourceV f g : ComplexEuclidean 1) :
    -((radius : ℂ)⁻¹ • x) - (Complex.I * (((mode.2 : ℝ) / length) : ℝ)) • (c + sourceC) -
      (Complex.I * (mode.1 : ℂ)) • ((radius : ℂ)⁻¹ • (v + sourceV)) +
      (Complex.I * (mode.1 : ℂ)) • g =
    (rawOriginalUnknownRHS length radius mode x j c v +
      rawOriginalSourceRHS length radius mode sourceJ sourceC sourceV f g).1 := by
  apply PiLp.ext
  intro entry
  simp only [rawOriginalUnknownRHS, rawOriginalSourceRHS, Prod.fst_add,
    frequencyNumerator, PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
  push_cast
  simp only [div_eq_mul_inv]
  ring

/-- Literal full high second-row fidelity for the SAME original smooth-source inverse. -/
theorem generalSharedHighXRHS_actual (mode : HighAnnularMode) :
    generalSharedHighXRHS parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data mode
      =ᵐ[volume.restrict (Icc lower 1)] fun radius =>
        (generalOriginalFullRHS parameters length compact lower positive lowerHalf lengthPositive state data
          (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) radius mode.val).1 := by
  let field := sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  let row := fun index => lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state index
    (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data field)
  let x := highBulkIntoFull lower (field.ofLp.1.ofLp.2.val 0)
  let g := (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2
  have literal : generalSharedHighXRHS parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data mode =
      collarScalar 1 lower (rawHighPhase parameters lower positive mode.val.2)
        (-collarScalar 1 lower (highReciprocalRadius lower positive)
            (radialOrdinary 1 lower positive (x mode.val)) -
          (Complex.I * (((mode.val.2 : ℝ) / length) : ℝ)) • radialOrdinary 1 lower positive (row 1 mode.val) -
          (Complex.I * (mode.val.1 : ℂ)) • collarScalar 1 lower (highReciprocalRadius lower positive)
            (radialOrdinary 1 lower positive (row 2 mode.val)) +
          (Complex.I * (mode.val.1 : ℂ)) • radialOrdinary 1 lower positive (g mode.val)) := by
    change rawHighXPacketRHS parameters lower length positive
      (fullStrongHighPacket parameters length compact lower positive lowerHalf lengthPositive state data field) mode = _
    rw [rawHighXPacketRHS_full_sources]
    have same := sharedStrongResponse_sameFlux parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
    change field.ofLp.1.ofLp.2.val 0 = highPhysicalOutput lower 0
      (fullStrongHighPacket parameters length compact lower positive lowerHalf lengthPositive state data field) at same
    have sameMode := congrArg (fun value : AnnularBulk lower => value mode) same
    have xMode : x mode.val = field.ofLp.1.ofLp.2.val 0 mode :=
      highBulkIntoFull_high lower (field.ofLp.1.ofLp.2.val 0) mode
    exact congrArg (fun storedX : RadialL2 1 lower =>
      collarScalar 1 lower (rawHighPhase parameters lower positive mode.val.2)
        (-collarScalar 1 lower (highReciprocalRadius lower positive)
            (radialOrdinary 1 lower positive storedX) -
          (Complex.I * (((mode.val.2 : ℝ) / length) : ℝ)) • radialOrdinary 1 lower positive (row 1 mode.val) -
          (Complex.I * (mode.val.1 : ℂ)) • collarScalar 1 lower (highReciprocalRadius lower positive)
            (radialOrdinary 1 lower positive (row 2 mode.val)) +
          (Complex.I * (mode.val.1 : ℂ)) • radialOrdinary 1 lower positive (g mode.val)))
      (sameMode.symm.trans xMode.symm)

  rw [literal]
  filter_upwards [rawHighFlux_full_decode parameters length lower positive x (row 1) (row 2) g mode.val,
    fullStrongPhysicalCoefficient_split parameters length compact lower lengthPositive positive (lowerHalf.trans (by norm_num)) state data field 1,
    fullStrongPhysicalCoefficient_split parameters length compact lower lengthPositive positive (lowerHalf.trans (by norm_num)) state data field 2,
    sameCoupledXCoefficient_high_stored parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive field mode]
    with radius decoded splitC splitV sameX
  rw [decoded]
  change -((radius : ℂ)⁻¹ • lowRhoPhysicalCoefficient parameters lower positive
    (highBulkIntoFull lower (field.ofLp.1.ofLp.2.val 0)) radius mode.val) - _ - _ + _ = _
  rw [sameX]
  rw [show lowRhoPhysicalCoefficient parameters lower positive (row 1) radius mode.val = _ from splitC mode.val,
    show lowRhoPhysicalCoefficient parameters lower positive (row 2) radius mode.val = _ from splitV mode.val]
  exact generalHighFlux_source_split length radius mode.val _ _ _ _ _ _ _ _ _

end Grad.AnnularGeneralSourceRegularity
