import AKAF3SameCovariantGenuineAngularLaw

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.ActualPolarEquations
open Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.AnnularWeightedSmoothness
open Grad.AnnularGeneralSourceRegularity Grad.AnnularOriginalCoreRealization Grad.AnnularReconstruction
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.AnnularRestriction Grad.AnnularPhysicalReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularStrongOrbit Grad.AnnularHighGenerators
open Grad.AnnularFullGraph Grad.AnnularWeakExhaustion Grad.AnnularCoupledInverse
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation
open Grad.GaugeCoefficients.Physical.Allocation

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

/-- The actual original observed Cartesian-source solution has the genuine
classical angular derivative of its SAME polar covariant reconstruction. -/
theorem actualObservedCovariant_classical_angular
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (polar axial : ℝ) :
    HasDerivAt (fun angle =>
      (actualObservedPolarCurves parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades).fullField
          (lowerHalf.trans_lt (by norm_num)) (radius,angle,axial))
      (((actualCartesianSevenCurves parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades).rotatedCovariant
          parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state.val).fullField
            (lowerHalf.trans_lt (by norm_num)) (radius,polar,axial)) polar := by
  exact sharedCovariant_classical_angular parameters length compact lower positive
    (lowerHalf.trans_lt (by norm_num)) lengthPositive state.val
    (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0
      (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
        coefficientSmall lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat))
    (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive point.ofLp.1)
    (actualCartesianSevenCurves parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades)
    radius inside polar axial

end Grad.ActualPolarEquations
