import AKDN23GenuineNativeHigherEulerEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped ContDiff
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularWeightedSmoothness
open Grad.AnnularGeneralSourceRegularity Grad.AnnularKernelL2 Grad.AnnularCurrentLow
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularWeightedSystem Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularOriginalCoreRealization

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

local notation "phaseCurve" => sameNativeBalancedPhaseCurve parameters length compact lower positive lowerHalf lengthPositive
  widthHalf widthLength state small data
local notation "fluxCurve" => sameNativeBalancedFluxCurve parameters length compact lower positive lowerHalf lengthPositive
  widthHalf widthLength state small data
local notation "knownCurve" => fun grade radius => balancedActualSource parameters length compact lower positive bounded state data curves grade
  (collarRadius lower positive (le_of_lt bounded) radius)

include curves

/-- The SAME native diagonal phase contribution consumes just one next
frequency grade in every term of its genuine Euler expansion. -/
theorem sameNativeBalancedPhaseCurve_EulerBound (grade rank : ℕ) (radius : RadialPoint)
    (inside : radius.val ∈ Icc lower 1) :
    ‖vectorEulerWithinIteratedDerivative (Icc lower 1) rank (phaseCurve grade) radius.val‖ ≤
      eulerAllocationSum (fun order inputRank => balancedPhaseEulerConstant parameters order *
        ‖vectorEulerWithinIteratedDerivative (Icc lower 1) inputRank (balanced (grade+1)) radius.val‖) (eulerLeibnizTerms rank) := by
  have regular := sameNativeBalanced_smooth parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small data curves allGrades
  have firstSame (power reserve : ℕ) (point : ℝ) (member : point ∈ Icc lower 1) (mode : ℤ × ℤ) :
      (balanced (power+reserve) point).1 mode = (annularFrequency mode.1 mode.2 : ℂ)^reserve • (balanced power point).1 mode :=
    congrArg Prod.fst (balancedOriginalPairCurve_shift parameters lower length positive bounded lengthPositive response allGrades
      power reserve point member mode)
  have secondSame (power reserve : ℕ) (point : ℝ) (member : point ∈ Icc lower 1) (mode : ℤ × ℤ) :
      (balanced (power+reserve) point).2 mode = (annularFrequency mode.1 mode.2 : ℂ)^reserve • (balanced power point).2 mode :=
    congrArg Prod.snd (balancedOriginalPairCurve_shift parameters lower length positive bounded lengthPositive response allGrades
      power reserve point member mode)
  have firstBound := actualPhaseCurve_EulerOneOrder parameters lower positive bounded
    (fun power point => (balanced power point).1) (fun power => (regular power).fst) firstSame grade rank radius inside
  have secondBound := actualPhaseCurve_EulerOneOrder parameters lower positive bounded
    (fun power point => (balanced power point).2) (fun power => (regular power).snd) secondSame grade rank radius inside
  have firstPaid := firstBound.trans (eulerAllocationSum_mono _
    (fun order inputRank => balancedPhaseEulerConstant parameters order *
      ‖vectorEulerWithinIteratedDerivative (Icc lower 1) inputRank (balanced (grade+1)) radius.val‖)
    (eulerLeibnizTerms rank) (by
      intro term _
      apply mul_le_mul_of_nonneg_left _ (balancedPhaseEulerConstant_nonnegative parameters term.1)
      have observed := vectorEulerWithin_observation (Icc lower 1) (uniqueDiffOn_Icc bounded)
        (balanced (grade+1)) (ContinuousLinearMap.fst ℝ (CellL2 1) (CellL2 1)) term.2
        (contDiffOn_infty.mp (regular _) term.2) inside
      change vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 (fun point => (balanced (grade+1) point).1) radius.val =
        (vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 (balanced (grade+1)) radius.val).1 at observed
      rw [observed]
      exact norm_fst_le _))
  have secondPaid := secondBound.trans (eulerAllocationSum_mono _
    (fun order inputRank => balancedPhaseEulerConstant parameters order *
      ‖vectorEulerWithinIteratedDerivative (Icc lower 1) inputRank (balanced (grade+1)) radius.val‖)
    (eulerLeibnizTerms rank) (by
      intro term _
      apply mul_le_mul_of_nonneg_left _ (balancedPhaseEulerConstant_nonnegative parameters term.1)
      have observed := vectorEulerWithin_observation (Icc lower 1) (uniqueDiffOn_Icc bounded)
        (balanced (grade+1)) (ContinuousLinearMap.snd ℝ (CellL2 1) (CellL2 1)) term.2
        (contDiffOn_infty.mp (regular _) term.2) inside
      change vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 (fun point => (balanced (grade+1) point).2) radius.val =
        (vectorEulerWithinIteratedDerivative (Icc lower 1) term.2 (balanced (grade+1)) radius.val).2 at observed
      rw [observed]
      exact norm_snd_le _))
  have phaseSmooth : ContDiffOn ℝ rank (phaseCurve grade) (Icc lower 1) :=
    contDiffOn_infty.mp (sameNativeBalancedPhaseCurve_smooth parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data curves allGrades grade) rank
  have pairSame := vectorEulerWithin_pair (Icc lower 1) (uniqueDiffOn_Icc bounded)
    (fun point => (phaseCurve grade point).1) (fun point => (phaseCurve grade point).2) rank
    phaseSmooth.fst phaseSmooth.snd radius.val inside
  change vectorEulerWithinIteratedDerivative (Icc lower 1) rank (phaseCurve grade) radius.val = _ at pairSame
  rw [pairSame,Prod.norm_def]
  exact max_le firstPaid secondPaid

end Grad.OriginalCartesianTameEstimate
