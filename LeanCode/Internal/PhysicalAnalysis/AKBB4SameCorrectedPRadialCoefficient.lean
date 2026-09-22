import AKBB3SameOriginalXPrimitiveCurve

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarFlux
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators
open Grad.ActualPolarEquations Grad.BoundaryKernelAction
open Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularKernelL2 Grad.AnnularWeightedSmoothness

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

variable
    (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data
        (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)))

include curves allGrades

/-- The genuine original radial equation differentiates the SAME corrected
flux coefficients through their exact constant angular primitive. -/
theorem sharedCorrectedP_radialCoefficient (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    HasDerivWithinAt
      (fun current => (seven.correctedP parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state).physicalCurve 0 current mode)
      (angularInverseMultiplier mode •
        (generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data
          (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
          curves allGrades mode radius).1) (Icc lower 1) radius := by
  let response := sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  have regular := generalShared_phaseWeighted_radial parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small data curves allGrades
  have actual := generalShared_physical_derivative parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small data curves allGrades mode radius inside
  have first := (ContinuousLinearMap.fst ℝ (ComplexEuclidean 1) (ComplexEuclidean 1)).hasFDerivAt.comp_hasDerivWithinAt radius actual
  have scaled := first.const_smul (angularInverseMultiplier mode)
  have same (current : ℝ) (member : current ∈ Icc lower 1) :=
    sharedCorrectedP_originalXCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
      data response allGrades regular seven compact state current member mode
  apply scaled.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with current member
    exact same current member
  · exact same radius inside

end Grad.ActualPolarFlux
