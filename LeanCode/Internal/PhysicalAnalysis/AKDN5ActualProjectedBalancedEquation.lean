import AKDN4LiteralCombinedBalancedRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularWeightedSmoothness
open Grad.AnnularGeneralSourceRegularity Grad.AnnularKernelL2 Grad.AnnularCurrentLow
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularWeightedSystem Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (curves : ActualSourceRadialCurves parameters lower positive (lowerHalf.trans_lt (by norm_num)) data)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade
        (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) weighted)

local notation "response" => sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
local notation "bounded" => lowerHalf.trans_lt (by norm_num : (1:ℝ)/2<1)
local notation "balanced" => balancedOriginalPairCurve parameters lower length positive bounded lengthPositive response
local notation "pair" => conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive response
local notation "unknownRow" => balancedUnknownPhysicalRow parameters length compact lower positive bounded lengthPositive state response
local notation "knownRow" => generalConjugatedKnownRowCurve parameters length compact lower positive bounded state data curves
local notation "rhs" => generalConjugatedSystemRHS parameters length compact lower positive lowerHalf lengthPositive state data response curves

include allGrades

/-- The actual native balanced equation, with the literal outer angular
projection, the original phase, and the same known and unknown rows. -/
theorem sameNativeBalancedHilbertRHS_coefficient (grade : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    let row := fun index : Fin 3 => unknownRow index grade radius mode+knownRow index (grade+1) radius mode
    let phase : ℂ := (radius : ℂ)*(Grad.AnnularVariational.annularPhaseSlope parameters mode.2 radius : ℂ)-1
    hilbertPairCoefficient mode (sameNativeBalancedHilbertRHS parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data curves grade radius) =
      (if mode.1=0 then (0 : ℂ) else 1) •
        (phase • (balanced grade radius).1 mode+row 0+curves.force (grade+1) radius mode,
         phase • (balanced grade radius).2 mode-
          ((radius : ℂ)*(length : ℂ)⁻¹) • (frequencyRatioSymbol (some true) mode • row 1)-
          frequencyRatioSymbol (some false) mode • row 2+
          frequencyRatioSymbol (some false) mode • curves.third (grade+1) radius mode) := by
  dsimp only
  have same := balancedOriginalPairCurve_shift parameters lower length positive bounded lengthPositive response allGrades grade 1 radius inside
  have first : ∀ query, (balanced (grade+1) radius).1 query = (annularFrequency query.1 query.2 : ℂ) • (balanced grade radius).1 query := by
    intro query
    have actual := congrArg Prod.fst (same query)
    change (balanced (grade+1) radius).1 query = (annularFrequency query.1 query.2 : ℂ)^1 • (balanced grade radius).1 query at actual
    simpa only [pow_one] using actual
  have second : ∀ query, (balanced (grade+1) radius).2 query = (annularFrequency query.1 query.2 : ℂ) • (balanced grade radius).2 query := by
    intro query
    have actual := congrArg Prod.snd (same query)
    change (balanced (grade+1) radius).2 query = (annularFrequency query.1 query.2 : ℂ)^1 • (balanced grade radius).2 query at actual
    simpa only [pow_one] using actual
  have current := generalConjugatedSystemRHS_combinedRows parameters length compact lower positive lowerHalf lengthPositive
    state data response curves allGrades grade radius inside mode
  have next := generalConjugatedSystemRHS_combinedRows parameters length compact lower positive lowerHalf lengthPositive
    state data response curves allGrades (grade+1) radius inside mode
  dsimp only at current next
  have currentFirst := congrArg Prod.fst current
  have nextSecond := congrArg Prod.snd next
  change (rhs grade radius).1 mode = _ at currentFirst
  change (rhs (grade+1) radius).2 mode = _ at nextSecond
  change (balancedPhaseAction parameters 1 (collarRadius lower positive (bounded).le radius) (balanced (grade+1) radius).1 mode+
      (rhs (grade+1) radius).2 mode,
    balancedPhaseAction parameters 1 (collarRadius lower positive (bounded).le radius) (balanced (grade+1) radius).2 mode+
      (balanced grade radius).2 mode+radius • (rhs grade radius).1 mode) = _
  rw [balancedPhaseAction_same parameters 1 _ _ _ first mode,balancedPhaseAction_same parameters 1 _ _ _ second mode,
    collarRadius_literal lower positive (bounded).le radius inside,currentFirst,nextSecond]
  by_cases zero : mode.1=0
  · have mean := balancedOriginalPairCurve_meanZero parameters lower length positive bounded lengthPositive response allGrades grade radius inside mode.2
    have firstZero := congrArg Prod.fst mean
    have secondZero := congrArg Prod.snd mean
    have modeSame : mode=(0,mode.2) := Prod.ext zero rfl
    change (balanced grade radius).1 (0,mode.2)=0 at firstZero
    change (balanced grade radius).2 (0,mode.2)=0 at secondZero
    simp only [zero,ite_true,zero_smul,Prod.fst_zero,Prod.snd_zero,smul_zero,add_zero]
    rw [modeSame,firstZero,secondZero]
    simp only [smul_zero,zero_add]
    rfl
  · simp only [zero,ite_false,one_smul]
    have unknown := balancedUnknownPhysicalRow_shift parameters length compact lower positive bounded lengthPositive state response allGrades 0 grade 1 radius inside mode
    have known := actualKnownPhysicalRow_shift parameters length compact lower positive bounded state data curves 0 (grade+1) 1 radius inside mode
    simp only [pow_one] at unknown known
    rw [unknown,known]
    have frequencyNonzero : (annularFrequency mode.1 mode.2 : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Grad.SourceBoundaryTrace.annularFrequency_pos mode).ne'
    have radiusNonzero : (radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (positive.trans_le inside.1).ne'
    apply Prod.ext
    · apply PiLp.ext
      intro coordinate
      simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,frequencyRatioSymbol]
      field_simp
      ring
    · change _+(pair grade radius).1 mode+radius • _ = _
      apply PiLp.ext
      intro coordinate
      simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,←Complex.coe_smul,smul_eq_mul]
      field_simp
      ring

end Grad.OriginalCartesianTameEstimate
