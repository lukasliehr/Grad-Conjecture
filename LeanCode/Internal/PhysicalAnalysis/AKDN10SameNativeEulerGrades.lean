import AKDN6SameActualBalancedConsumer
import AKDN9FiniteActualEulerLeibniz

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

/-- Genuine Euler derivatives of the same native balanced curve. -/
def sameNativeBalancedEuler (grade rank : ℕ) (radius : ℝ) : PhysicalHilbertPair :=
  vectorEulerWithinIteratedDerivative (Icc lower 1) rank (balanced grade) radius

include curves

/-- Tangential grades commute with genuine Euler derivatives after bounded
coefficient observation. This uses the actual native all-order regularity. -/
theorem sameNativeBalancedEuler_shift (grade reserve rank : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    hilbertPairCoefficient mode (sameNativeBalancedEuler parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data (grade+reserve) rank radius) =
      (annularFrequency mode.1 mode.2 : ℂ)^reserve •
        hilbertPairCoefficient mode (sameNativeBalancedEuler parameters length compact lower positive lowerHalf lengthPositive
          widthHalf widthLength state small data grade rank radius) := by
  let observe := (hilbertPairCoefficient mode).restrictScalars ℝ
  let shifted := (((annularFrequency mode.1 mode.2 : ℂ)^reserve) • hilbertPairCoefficient mode).restrictScalars ℝ
  have highRegular : ContDiffOn ℝ rank (balanced (grade+reserve)) (Icc lower 1) :=
    contDiffOn_infty.mp (sameNativeBalanced_smooth parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data curves allGrades (grade+reserve)) rank
  have lowRegular : ContDiffOn ℝ rank (balanced grade) (Icc lower 1) :=
    contDiffOn_infty.mp (sameNativeBalanced_smooth parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data curves allGrades grade) rank
  have highObserved := vectorEulerWithin_observation (Icc lower 1) (uniqueDiffOn_Icc bounded)
    (balanced (grade+reserve)) observe rank highRegular inside
  have lowObserved := vectorEulerWithin_observation (Icc lower 1) (uniqueDiffOn_Icc bounded)
    (balanced grade) shifted rank lowRegular inside
  change _ = observe _ at highObserved
  change _ = shifted _ at lowObserved
  change observe (vectorEulerWithinIteratedDerivative (Icc lower 1) rank (balanced (grade+reserve)) radius) =
    shifted (vectorEulerWithinIteratedDerivative (Icc lower 1) rank (balanced grade) radius)
  rw [←highObserved,←lowObserved]
  apply vectorEulerWithin_congr (Icc lower 1) rank _ _ _ inside
  intro point member
  exact balancedOriginalPairCurve_shift parameters lower length positive bounded lengthPositive response allGrades grade reserve point member mode

/-- Genuine adjacent Euler jets retain the same native curve and the
closed-collar derivative, including the outer boundary. -/
theorem sameNativeBalancedEuler_derivative (grade rank : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (sameNativeBalancedEuler parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data grade rank)
      (radius⁻¹ • sameNativeBalancedEuler parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small data grade (rank+1) radius) (Icc lower 1) radius :=
  vectorEulerWithin_jetDerivative (Icc lower 1) (uniqueDiffOn_Icc bounded) (balanced grade) rank
    (contDiffOn_infty.mp (sameNativeBalanced_smooth parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data curves allGrades grade) (rank+1)) radius inside
    (positive.trans_le inside.1).ne'

end Grad.OriginalCartesianTameEstimate
