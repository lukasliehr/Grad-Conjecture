import AKAT16SameLiteralCartesianThird
import AKAK20ActualCartesianSourceRadialConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open Set
open scoped ContDiff
namespace Grad.ActualCartesianEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra
open Grad.AnnularHighGenerators Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow

open Grad.AnnularGeneralSourceRegularity Grad.ActualSmoothPhysicalField

open Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation

open Grad.ActualPolarEquations Grad.ActualPolarFlux Grad.SourceCollarFullSource

/-- The original coupled equation yields literal AM19 for the SAME Cartesian fields. -/
theorem actualCartesianEquation_third
    (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (coefficientSmall : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 6 ≤
      originalCoefficientLowRadius parameters length)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (data : OriginalStrongCarrier parameters lower 0 0)
    (candidate : OriginalCoupledSpace lower length positive)
    (equation : OriginalStrongCoupledEquation parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state data candidate)
    (sameSources : data.val.ofLp.1 =
      (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
        lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat).val.ofLp.1)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade
        (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate) weighted)
    (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data) (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate))) :
    ∀ (radius : ℝ) (inside : radius ∈ Ioo lower 1) (angles : ℝ × ℝ),
    sameCartesianThirdExpression parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state
      (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)
      (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate) seven
      radius ⟨inside.1.le,inside.2.le⟩ angles.1 angles.2 =
        (length : ℂ) * (seven.bulkUnit (0 : Fin 1) 6).fullField (lowerHalf.trans_lt (by norm_num)) (radius,angles) 0 := by
  have smooth := actualCartesianEquation_phaseWeighted_radial parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
    state small coefficientSmall source flat data candidate equation sameSources allGrades
  intro radius inside angles
  exact sameCartesianThirdExpression_eq parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state
    (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)
    (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate) seven
    allGrades smooth radius inside angles.1 angles.2

end Grad.ActualCartesianEquations
