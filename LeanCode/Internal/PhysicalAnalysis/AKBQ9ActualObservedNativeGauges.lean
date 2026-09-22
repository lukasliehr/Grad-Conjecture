import AKBQ7OriginalPacketScaledGaugeMeans

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.ActualScaledNativeCoefficients
open Grad.ActualSmoothPhysicalField Grad.OriginalKernelCovariantRecovery Grad.CartesianStartup Grad.BoundaryTrace Grad.AnnularOriginalSmoothCore
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


/-- The exact observed original source solution has both literal native gauge means on each collar. -/
theorem actualObservedPolarCurves_gaugeMeans (radius : Icc lower (1 : ℝ)) (kind : Fin 2) (cell : ℤ) :
    angularCoefficient (fun polar => angularCoefficient (fun axial =>
      originalTotalGaugeProduct parameters length compact state.val.val (tupleRadius lower positive radius) kind
        (fun angles => (actualObservedPolarCurves parameters length compact lower positive lowerHalf lengthPositive
          widthHalf widthLength state small coefficientSmall source flat point member sameSources allGrades).fullField
          (lowerHalf.trans_lt (by norm_num)) (radius.val,angles)) (polar,axial)) cell) 0 = 0 :=
  startupNative_originalPacket_physicalGaugeMean parameters length compact lower positive
    (lowerHalf.trans_lt (by norm_num)) lengthPositive state.val
    (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
      lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat) point.ofLp.1
    (actualCartesianSevenCurves parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
      state small coefficientSmall source flat point member sameSources allGrades) radius kind cell

end Grad.ActualScaledNativeCoefficients
