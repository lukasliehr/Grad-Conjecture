import AKAK7SamePhysicalXiRadialPDE

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators
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
    (force : SmoothLowPhysicalRow parameters lower positive
      (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) data 3))

include curves allGrades

/-- Any genuine smooth representatives of the SAME prescribed rows give
exactly the already proved Xi radial equation. -/
theorem sharedPhysicalXi_radial_with_rows (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    HasDerivWithinAt
      (fun current => originalPhysicalComponentField parameters lower length positive
        (lowerHalf.trans_lt (by norm_num)) lengthPositive
        (sharedStrongResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
        1 (current,angles))
      (((SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 0).add force).meanFree.fullField
        (lowerHalf.trans_lt (by norm_num)) (radius,angles)) (Icc lower 1) radius := by
  have derivative := sharedPhysicalXi_radial parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small data curves allGrades radius inside angles
  have equal := samePhysical_fullField_eq
    (sharedActualXiRadialRHS parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data curves allGrades).meanFree
    ((SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 0).add force).meanFree
    (lowerHalf.trans_lt (by norm_num)) (Filter.Eventually.of_forall (fun _ _ => rfl)) radius inside angles
  rw [equal] at derivative
  exact derivative

end Grad.ActualPolarEquations
