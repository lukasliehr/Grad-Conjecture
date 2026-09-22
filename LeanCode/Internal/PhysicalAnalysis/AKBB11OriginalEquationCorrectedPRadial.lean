import AKBB10SameCorrectedPClassicalRadial

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open Set
open scoped ContDiff
namespace Grad.ActualPolarFlux
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra
open Grad.AnnularHighGenerators Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow

open Grad.AnnularGeneralSourceRegularity Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations

private theorem weightedEquation_correctedPRadial
    (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (candidate : CoupledSpace lower length positive lengthPositive)
    (same : candidate = sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
    (curves : ActualSourceRadialCurves parameters lower positive (lowerHalf.trans_lt (by norm_num))
      data)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade
        candidate weighted)
    (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data candidate))
    (third : SmoothLowPhysicalRow parameters lower positive
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    HasDerivWithinAt
      (fun current => (seven.correctedP parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state).fullField
        (lowerHalf.trans_lt (by norm_num)) (current,angles))
      (primitiveDeterminantRHS length radius
        (actualPrimitiveDeterminantFields parameters length compact lower positive lowerHalf lengthPositive state data candidate seven third radius) angles)
      (Icc lower 1) radius := by
  subst candidate
  exact sharedCorrectedP_radial parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
    state small data curves allGrades seven third radius inside angles

/-- The actual original coupled equation implies the genuine corrected-flux radial
equation for the SAME field; all incoming and source data are retained. -/
theorem originalEquation_correctedPRadial
    (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (data : OriginalStrongCarrier parameters lower 0 0)
    (candidate : OriginalCoupledSpace lower length positive)
    (equation : OriginalStrongCoupledEquation parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state data candidate)
    (curves : ActualSourceRadialCurves parameters lower positive (lowerHalf.trans_lt (by norm_num))
      (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data))
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade
        (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate) weighted)
    (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data) (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate)))
    (third : SmoothLowPhysicalRow parameters lower positive
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)).ofLp.1.ofLp.2)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    HasDerivWithinAt
      (fun current => (seven.correctedP parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state).fullField
        (lowerHalf.trans_lt (by norm_num)) (current,angles))
      (primitiveDeterminantRHS length radius
        (actualPrimitiveDeterminantFields parameters length compact lower positive lowerHalf lengthPositive state (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data) (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate) seven third radius) angles)
      (Icc lower 1) radius := by
  let weightedData := originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data
  let field := originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate
  have same : field = sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small weightedData :=
    sharedStrongResponse_unique parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small weightedData field equation
  exact weightedEquation_correctedPRadial parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
    state small weightedData field same curves allGrades seven third radius inside angles

end Grad.ActualPolarFlux
