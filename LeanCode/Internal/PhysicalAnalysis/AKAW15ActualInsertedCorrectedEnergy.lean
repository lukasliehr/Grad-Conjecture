import AKAW11FullSevenInsertedTransport
import AKAW14CorrectedCollarEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.ActualNativeCellMoments
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.AnnularWeightedSmoothness
open Grad.AnnularGeneralSourceRegularity Grad.AnnularOriginalCoreRealization Grad.AnnularReconstruction
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.AnnularRestriction Grad.AnnularPhysicalReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularStrongOrbit Grad.AnnularHighGenerators
open Grad.AnnularFullGraph Grad.AnnularWeakExhaustion Grad.AnnularCoupledInverse
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation
open Grad.GaugeCoefficients.Physical.Allocation Grad.ActualSmoothPhysicalField Grad.AnnularExhaustionEstimate

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


/-- Actual inserted native coordinates pay the SAME corrected physical curve
at every finite Fourier grade. No graded PDE or Cartesian L2 hypothesis is used. -/
theorem actualObservedPhysicalU_insertedEnergy (grade : ℕ)
    (weighted : CoupledSpace lower length positive lengthPositive)
    (same : CoupledInsertedGrade lower length positive lengthPositive grade
      (originalWeightedRetainedObservation parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive point) weighted)
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (coefficientBound : ∀ (inner : ℝ) (innerPositive : 0 < inner) (innerBounded : inner < 1)
      (row : DivisionRow 7 inner) (curves : SmoothLowPhysicalRow parameters inner innerPositive row) (radius : ℝ),
      ‖((curves.covariant parameters length compact inner innerPositive innerBounded state.val).physicalUFromPolar
        parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall inner innerPositive innerBounded).curve grade radius‖ ≤
          constant * ‖curves.curve grade radius‖) :
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖(actualObservedPhysicalUCurves parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small coefficientSmall
        source flat point member sameSources allGrades).curve grade radius‖ ^ 2)) ≤
      ENNReal.ofReal ((constant * ((11 + 4 * length) * ‖weighted‖ +
        3 * ‖originalWeightedDatum parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive
          (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
            lower positive (lowerHalf.trans_lt (by norm_num)) grade source flat)‖)) ^ 2) := by
  let lowerBounded : lower < 1 := lowerHalf.trans_lt (by norm_num)
  let data := actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
    lower positive lowerBounded 0 source flat
  let gradedData := actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
    lower positive lowerBounded grade source flat
  let weightedData := originalWeightedDatum parameters lower length positive lowerBounded.le lengthPositive data
  let weightedGradedData := originalWeightedDatum parameters lower length positive lowerBounded.le lengthPositive gradedData
  let native := originalWeightedRetainedObservation parameters lower length positive lowerBounded.le lengthPositive point
  let packet := fullStrongSevenInput parameters length lower lengthPositive positive lowerBounded.le weightedData native
  let gradedPacket := fullStrongSevenInput parameters length lower lengthPositive positive lowerBounded.le weightedGradedData weighted
  let curves := actualCartesianSevenCurves parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small coefficientSmall
    source flat point member sameSources allGrades
  have sameData := actualOriginalSourceDatum_inserted parameters length state.val.val.rho state.val.val.epsilon lengthPositive state.val.val.field
    coefficientSmall lower positive lowerBounded grade source flat
  have packetSame := fullSevenPacket_inserted parameters lower length positive lowerBounded.le lengthPositive grade native weighted
    weightedData weightedGradedData same sameData
  have energy := curveEnergy_transfer parameters lower positive packet curves grade gradedPacket packetSame
    ((actualObservedPhysicalUCurves parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small coefficientSmall
      source flat point member sameSources allGrades).curve grade) constant nonnegative
    (fun radius _ => coefficientBound lower positive lowerBounded packet curves radius)
  have packetBound := fullStrongSevenInput_bound parameters length lower lengthPositive positive lowerBounded.le weightedGradedData weighted
  apply energy.trans
  apply ENNReal.ofReal_le_ofReal
  apply (sq_le_sq₀ (mul_nonneg nonnegative (norm_nonneg _)) (mul_nonneg nonnegative (by positivity))).mpr
  exact mul_le_mul_of_nonneg_left packetBound nonnegative

end Grad.ActualNativeCellMoments
