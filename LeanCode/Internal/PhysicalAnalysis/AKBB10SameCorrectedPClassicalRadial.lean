import AKBB9SameScalarRadialSynthesis

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

variable (third : SmoothLowPhysicalRow parameters lower positive
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2)

include curves allGrades

/-- Genuine classical p radial equation for the SAME corrected flux and
original b3,rV,G3, with the original outer mean projection intact. -/
theorem sharedCorrectedP_radial (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    HasDerivWithinAt
      (fun current => (seven.correctedP parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state).fullField
        (lowerHalf.trans_lt (by norm_num)) (current,angles))
      (primitiveDeterminantRHS length radius
        (actualPrimitiveDeterminantFields parameters length compact lower positive lowerHalf lengthPositive state data
          (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
          seven third radius) angles) (Icc lower 1) radius := by
  let response := sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  let fields := actualPrimitiveDeterminantFields parameters length compact lower positive lowerHalf lengthPositive state data response seven third radius
  have smooth := actualPrimitiveDeterminantFields_smooth parameters length compact lower positive lowerHalf lengthPositive state data response seven third radius inside
  have angular := actualPrimitiveDeterminantFields_angular parameters length compact lower positive lowerHalf lengthPositive state data response seven third radius
  have cell := actualPrimitiveDeterminantFields_cell parameters length compact lower positive lowerHalf lengthPositive state data response seven third radius
  have periodic := primitiveDeterminantRHS_periodic length radius fields angular cell
  apply fullScalarField_radial_of_doubleCoefficients
    (seven.correctedP parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state)
    (lowerHalf.trans_lt (by norm_num)) radius inside
    (fun mode => angularInverseMultiplier mode •
      (generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data response curves allGrades mode radius).1)
    (fun mode => sharedCorrectedP_radialCoefficient parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
      state small data curves allGrades seven radius inside mode)
    (primitiveDeterminantRHS length radius fields)
    (primitiveDeterminantRHS_continuous length radius fields smooth) periodic.1 periodic.2 _ angles
  intro mode
  rw [primitiveDeterminantRHS_coefficient length radius fields smooth cell mode]
  have represented (index : Fin 4) := actualPrimitiveDeterminantFields_coefficient parameters length compact lower positive lowerHalf lengthPositive
    state data response seven third radius inside index mode
  exact (congrArg (primitiveDeterminantModeRHS length radius mode) (funext represented)).trans
    (actualPrimitiveDeterminantSlope parameters length compact lower positive lowerHalf lengthPositive state data response seven third
      curves allGrades radius inside mode).symm

end Grad.ActualPolarFlux
