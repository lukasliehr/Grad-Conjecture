import AKAC29ActualObservedPhysicalCurves

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.AnnularWeightedSmoothness
open Grad.AnnularGeneralSourceRegularity Grad.AnnularOriginalCoreRealization Grad.AnnularReconstruction
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.AnnularRestriction Grad.AnnularPhysicalReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularStrongOrbit Grad.AnnularHighGenerators
open Grad.AnnularFullGraph Grad.AnnularWeakExhaustion Grad.AnnularCoupledInverse
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation
open Grad.GaugeCoefficients.Physical.Allocation Grad.SourceCollar Grad.SourceCollarFullSource
open Grad.GaugeCoefficients.Physical.Ledger Grad.AnnularClosedJointRegularity

variable
    (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (coefficientSmall : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 6 ≤
      originalCoefficientLowRadius parameters length)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (point : OriginalFiveBlockAmbient parameters lower length positive)
    (member : point ∈ OriginalObservedEquationGraph parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
    (sameSources : point.ofLp.2 =
      (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
        lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat).val.ofLp.1)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade
        (originalWeightedRetainedObservation parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive point) weighted)

/-- Exact pointwise recovery for the original-source SAME observed solution,
with original Cartesian frame, angular projection, width, and incoming datum. -/
theorem actualObservedPhysical_recovery (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    WithLp.toLp 2 ((originalPhysicalFrameMatrix parameters length state.val.val.epsilon state.val.val.field angles.2
      (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2)).transpose.mulVec
        ((actualObservedPhysicalUCurves parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades).fullField (lowerHalf.trans_lt (by norm_num)) (radius,angles))) =
      cartesianCovariantValue angles.1 ((actualObservedPolarCurves parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades).fullField (lowerHalf.trans_lt (by norm_num)) (radius,angles)) ∧
    (actualObservedSOverRadiusCurves parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades).fullField (lowerHalf.trans_lt (by norm_num)) (radius,angles) =
      (actualObservedXiOverRadiusCurves parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades).fullField (lowerHalf.trans_lt (by norm_num)) (radius,angles) +
        removePolarMean (fun angles => matrixUnit (0 : Fin 1) (1 : Fin 3)
          ((actualObservedPolarCurves parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades).fullField (lowerHalf.trans_lt (by norm_num)) (radius,angles))) angles := by
  constructor
  · exact (actualObservedPolarCurves parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades).fullField_originalFrameRecovery
      parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall lower positive
      (lowerHalf.trans_lt (by norm_num)) radius inside angles
  · exact (actualObservedXiOverRadiusCurves parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades).fullField_polarScalarOverRadius
      (lowerHalf.trans_lt (by norm_num)) (actualObservedPolarCurves parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades) radius inside angles

/-- Both corrected original fields are jointly smooth on each complete
closed annulus, with no finite-source or unknown smoothness premise. -/
theorem actualObservedCorrectedFields_smooth :
    ContDiffOn ℝ ∞ ((actualObservedPhysicalUCurves parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades).fullField (lowerHalf.trans_lt (by norm_num))) (annularJointClosed lower) ∧
    ContDiffOn ℝ ∞ ((actualObservedSOverRadiusCurves parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades).fullField (lowerHalf.trans_lt (by norm_num))) (annularJointClosed lower) :=
  ⟨(actualObservedPhysicalUCurves parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades).fullField_smooth (lowerHalf.trans_lt (by norm_num)),
    (actualObservedSOverRadiusCurves parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades).fullField_smooth (lowerHalf.trans_lt (by norm_num))⟩

end Grad.ActualSmoothPhysicalField
