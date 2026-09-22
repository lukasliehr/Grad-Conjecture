import AKV34ActualCartesianEquationRadialRegularity
import AKM9OriginalWeakLimitCoordinatesAndBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open Set
open scoped ContDiff
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra
open Grad.AnnularHighGenerators Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow

open Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation
open Grad.AnnularFullGraph Grad.AnnularWeakExhaustion
/-- Regularity of the same actual five-block observation; the original
four source coordinates are used and the incoming data are left exact. -/
theorem actualCartesianObserved_phaseWeighted_radial
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
        (originalWeightedRetainedObservation parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive point) weighted) :
    ∀ grade, ContDiffOn ℝ ∞
      (conjugatedOriginalPairCurve parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
        (originalWeightedRetainedObservation parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive point) grade)
      (Icc lower 1) := by
  obtain ⟨⟨data,candidate⟩,equation,rfl⟩ := member
  exact actualCartesianEquation_phaseWeighted_radial parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small coefficientSmall source flat data candidate equation sameSources allGrades

end Grad.AnnularGeneralSourceRegularity
