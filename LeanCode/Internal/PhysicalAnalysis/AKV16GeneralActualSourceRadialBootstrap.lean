import AKV15GenuineGeneralAllGradePDE

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
namespace Grad.AnnularGeneralSourceRegularity
open Grad.AnnularVariational
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra
open Grad.AnnularHighGenerators Grad.AnnularCurrentLow Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularHighRadial Grad.CircularHighRegularity Grad.AnnularLowClassical Grad.AnnularLowEnergy

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (curves : ActualSourceRadialCurves parameters lower positive (lowerHalf.trans_lt (by norm_num)) data)


variable (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
  CoupledInsertedGrade lower length positive lengthPositive grade (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) weighted)
include allGrades curves


open Grad.AnnularWeightedSystem Grad.AnnularWeightedSmoothness
open scoped ContDiff

/-- Actual original-width all-grade radial smoothness of the same shared
inverse for arbitrary source data with their genuine smooth radial curves.
No finite-source-core or solution derivative premise occurs. -/
theorem generalShared_phaseWeighted_radial :
    ∀ grade, ContDiffOn ℝ ∞
      (conjugatedOriginalPairCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) grade)
      (Icc lower 1) := by
  classical
  have common (order grade : ℕ) := originalRows_commonReserve parameters length compact lower positive
    (lowerHalf.trans (by norm_num)) state (grade+1) order (order+3)
    (fun row => originalPhysicalRowKernel_finiteOrder parameters length compact state lower positive
      (lowerHalf.trans_lt (by norm_num)) row (grade+1) order)
  choose reserve enough rowsSmooth using common
  apply finiteReservePairScale_smooth lower (lowerHalf.trans_lt (by norm_num))
    (conjugatedOriginalPairCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data))
    (generalWeightedSystemSource parameters length compact lower positive lowerHalf state data curves)
    (fun order grade => grade+2+reserve order grade)
    (fun order grade => fullReservedWeightedSystemOperator parameters length compact lower positive lowerHalf state grade (reserve order grade))
  · exact fun grade => (conjugatedOriginalPairCurve_continuous parameters lower length positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) allGrades grade).continuousOn
  · exact generalWeightedSystemSource_smooth parameters length compact lower positive lowerHalf state data curves
  · intro order grade
    exact fullReservedWeightedSystemOperator_smooth parameters length compact lower positive lowerHalf state
      grade (reserve order grade) order (by have h := enough order grade; omega) (rowsSmooth order grade)
  · intro order grade mode radius inside
    have derivative := generalShared_weighted_derivative parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data curves allGrades grade mode radius inside
    rw [← generalReservedWeightedSystem_same parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades
      grade (reserve order grade) (by have h := enough order grade; omega) radius inside mode] at derivative
    exact derivative.fst
  · intro order grade mode radius inside
    have derivative := generalShared_weighted_derivative parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small data curves allGrades grade mode radius inside
    rw [← generalReservedWeightedSystem_same parameters length compact lower positive lowerHalf lengthPositive state data (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) curves allGrades
      grade (reserve order grade) (by have h := enough order grade; omega) radius inside mode] at derivative
    exact derivative.snd

end Grad.AnnularGeneralSourceRegularity
