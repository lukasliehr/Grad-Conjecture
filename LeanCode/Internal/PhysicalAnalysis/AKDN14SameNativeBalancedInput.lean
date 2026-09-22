import AKDN13ActualPhysicalRowEulerAllocation

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

/-- The SAME balanced native seven packet, at an arbitrary original
frequency grade, before any physical row operator is applied. -/
def sameNativeBalancedInput (grade : ℕ) (radius : ℝ) : CellL2 7 :=
  balancedSevenInput parameters radius (balanced grade radius)

include curves

theorem sameNativeBalancedInput_smooth (grade : ℕ) :
    ContDiffOn ℝ ∞ (sameNativeBalancedInput parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data grade) (Icc lower 1) := by
  have inputSmooth : ContDiff ℝ ∞ (balancedSevenInput parameters) := by
    rw [show balancedSevenInput parameters = fun point => balancedSevenInput parameters 0+point • balancedSevenInputSlope parameters from
      funext (balancedSevenInput_affine parameters)]
    exact contDiff_const.add (contDiff_id.smul contDiff_const)
  have realSmooth := ((ContinuousLinearMap.restrictScalarsIsometry ℂ PhysicalHilbertPair (CellL2 7) ℝ ℝ).toContinuousLinearMap.contDiff).comp_contDiffOn
    (inputSmooth.contDiffOn (s := Icc lower 1))
  exact realSmooth.clm_apply (sameNativeBalanced_smooth parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small data curves allGrades grade)

omit curves in
theorem sameNativeBalancedInput_shift (grade reserve : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1)
    (mode : ℤ × ℤ) :
    sameNativeBalancedInput parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data (grade+reserve) radius mode =
      (annularFrequency mode.1 mode.2 : ℂ)^reserve •
        sameNativeBalancedInput parameters length compact lower positive lowerHalf lengthPositive
          widthHalf widthLength state small data grade radius mode :=
  balancedSevenInput_sameGrade parameters radius reserve _ _
    (balancedOriginalPairCurve_shift parameters lower length positive bounded lengthPositive response allGrades grade reserve radius inside) mode

theorem sameNativeBalancedInput_EulerShift (grade reserve rank : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (sameNativeBalancedInput parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small data (grade+reserve)) radius mode =
      (annularFrequency mode.1 mode.2 : ℂ)^reserve •
        vectorEulerWithinIteratedDerivative (Icc lower 1) rank
          (sameNativeBalancedInput parameters length compact lower positive lowerHalf lengthPositive
            widthHalf widthLength state small data grade) radius mode :=
  cellCurveEuler_shift lower bounded _
    (sameNativeBalancedInput_smooth parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data curves allGrades)
    (sameNativeBalancedInput_shift parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data allGrades) grade reserve rank radius inside mode

omit allGrades curves in
theorem balancedUnknownPhysicalRow_sameNativeInput (row : Fin 3) (grade : ℕ) (radius : ℝ) :
    balancedUnknownPhysicalRow parameters length compact lower positive bounded lengthPositive state response row grade radius =
      radialConjugatedAction parameters lower positive (bounded).le
        (lowPhysicalRowKernel parameters length compact state row) (grade+1) 0 radius
        (sameNativeBalancedInput parameters length compact lower positive lowerHalf lengthPositive
          widthHalf widthLength state small data (grade+1) radius) := by
  rw [radialConjugatedAction_zero_apply]
  rfl

end Grad.OriginalCartesianTameEstimate
