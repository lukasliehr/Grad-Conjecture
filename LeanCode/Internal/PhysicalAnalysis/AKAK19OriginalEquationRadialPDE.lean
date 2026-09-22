import AKAK17SamePhysicalDeterminantRadialPDE
import AKAK18SameXiEquationForActualRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open Set
open scoped ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra
open Grad.AnnularHighGenerators Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow

open Grad.AnnularGeneralSourceRegularity Grad.ActualSmoothPhysicalField

private theorem weightedEquation_physicalRadialPDE
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
    (force : SmoothLowPhysicalRow parameters lower positive
      (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data 3))
    (third : SmoothLowPhysicalRow parameters lower positive
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    HasDerivWithinAt
      (fun current => originalPhysicalComponentField parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive candidate 0 (current,angles))
      (determinantPhysicalRHS length radius
        (actualDeterminantFields parameters length compact lower positive lowerHalf lengthPositive state data candidate seven third radius) angles)
      (Icc lower 1) radius ∧
    HasDerivWithinAt
      (fun current => originalPhysicalComponentField parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive candidate 1 (current,angles))
      (((SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 0).add force).meanFree.fullField
        (lowerHalf.trans_lt (by norm_num)) (radius,angles)) (Icc lower 1) radius := by
  subst candidate
  exact ⟨sharedPhysicalX_radial parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
    state small data curves allGrades seven third radius inside angles,
    sharedPhysicalXi_radial_with_rows parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
      state small data curves allGrades seven force radius inside angles⟩

/-- The actual original coupled equation implies both genuine physical radial
equations for the SAME field; all incoming and source data are retained. -/
theorem originalEquation_physicalRadialPDE
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
    (force : SmoothLowPhysicalRow parameters lower positive
      (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data) 3))
    (third : SmoothLowPhysicalRow parameters lower positive
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)).ofLp.1.ofLp.2)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    HasDerivWithinAt
      (fun current => originalPhysicalComponentField parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate) 0 (current,angles))
      (determinantPhysicalRHS length radius
        (actualDeterminantFields parameters length compact lower positive lowerHalf lengthPositive state (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data) (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate) seven third radius) angles)
      (Icc lower 1) radius ∧
    HasDerivWithinAt
      (fun current => originalPhysicalComponentField parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate) 1 (current,angles))
      (((SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 0).add force).meanFree.fullField
        (lowerHalf.trans_lt (by norm_num)) (radius,angles)) (Icc lower 1) radius := by
  let weightedData := originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data
  let field := originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate
  have same : field = sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small weightedData :=
    sharedStrongResponse_unique parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small weightedData field equation
  exact weightedEquation_physicalRadialPDE parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
    state small weightedData field same curves allGrades seven force third radius inside angles

end Grad.ActualPolarEquations
