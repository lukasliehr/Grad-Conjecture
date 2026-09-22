import AKAC28ActualCorrectedSourceEnergy

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

/-- Actual Cartesian-source polar covariant curves of the same full observed solution. -/
def actualObservedPolarCurves : SmoothLowPhysicalRow parameters lower positive
    (Grad.ActualPuncturedReconstruction.originalGraphCovariant parameters length compact lower positive
      (lowerHalf.trans (by norm_num)) lengthPositive state (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
      lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat) point) :=
  (actualCartesianSevenCurves parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades).covariant
    parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state.val

/-- Exact Xi/r coordinate of that same original seven packet. -/
def actualObservedXiOverRadiusCurves : SmoothLowPhysicalRow parameters lower positive
    (Grad.ActualPhysicalField.originalScalarOverRadius parameters length lower positive
      (lowerHalf.trans (by norm_num)) lengthPositive (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
      lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat) point) :=
  (actualCartesianSevenCurves parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades).bulkUnit (0 : Fin 1) (3 : Fin 7)

/-- Corrected physical U uses Q a_c before the actual Cartesian inverse. -/
def actualObservedPhysicalUCurves : SmoothLowPhysicalRow parameters lower positive
    (physicalUFromPolar parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall lower positive
      (lowerHalf.trans (by norm_num)) (Grad.ActualPuncturedReconstruction.originalGraphCovariant parameters length compact lower positive
      (lowerHalf.trans (by norm_num)) lengthPositive state (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
      lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat) point)) :=
  (actualObservedPolarCurves parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades).physicalUFromPolar
    parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall lower positive (lowerHalf.trans_lt (by norm_num))

/-- Genuine original S/r = Xi/r + P(a_c,2), with no erased angular product. -/
def actualObservedSOverRadiusCurves : SmoothLowPhysicalRow parameters lower positive
    (polarScalarOverRadiusRow lower (Grad.ActualPhysicalField.originalScalarOverRadius parameters length lower positive
      (lowerHalf.trans (by norm_num)) lengthPositive (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
      lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat) point) (Grad.ActualPuncturedReconstruction.originalGraphCovariant parameters length compact lower positive
      (lowerHalf.trans (by norm_num)) lengthPositive state (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
      lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat) point)) :=
  (actualObservedXiOverRadiusCurves parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades).polarScalarOverRadius
    (actualObservedPolarCurves parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades)

end Grad.ActualSmoothPhysicalField
