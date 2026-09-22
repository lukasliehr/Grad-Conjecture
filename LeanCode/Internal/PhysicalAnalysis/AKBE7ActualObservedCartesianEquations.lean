import AKBE6IncomingIndependentPhysicalExpressions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.ActualCartesianWeakEquations
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


open Grad.ActualSmoothPhysicalField Grad.ActualCartesianEquations Grad.ActualPolarEquations Grad.ActualPolarFlux Grad.SourceCollarFullSource Grad.AnnularExhaustionEstimate

variable (seven : SmoothLowPhysicalRow parameters lower positive
    (originalSevenPacket parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive
      (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat) point.ofLp.1))

include member sameSources allGrades small in
/-- The actual observed equation graph yields the literal Cartesian equations
for any genuine SAME canonical source packet. The original solved incoming
trace is kept in the proof and is never reset to the source datum's trace. -/
theorem actualObserved_originalForceAndThird :
    ∀ (radius : ℝ) (inside : radius ∈ Ioo lower 1) (angles : ℝ × ℝ),
      cartesianRadialMeanFree (fun query => sameCartesianRawForce parameters length compact lower positive
        (lowerHalf.trans_lt (by norm_num)) lengthPositive state
        (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat)) (originalWeightedRetainedObservation parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive point) seven
        radius ⟨inside.1.le,inside.2.le⟩ query.1 query.2) angles =
        cartesianRadialMeanFree (literalCartesianPlanarSource parameters source radius
          (positive.le.trans inside.1.le) inside.2.le) angles ∧
      sameCartesianThirdExpression parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state
        (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat)) (originalWeightedRetainedObservation parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive point) seven
        radius ⟨inside.1.le,inside.2.le⟩ angles.1 angles.2 =
        corePolarValue parameters (source 3) radius (positive.le.trans inside.1.le) inside.2.le angles 0 := by
  obtain ⟨⟨data,candidate⟩,equation,rfl⟩ := member
  simp only [originalFiveBlockObservation_retained] at seven
  simp only [originalWeightedRetainedObservation_apply,originalFiveBlockObservation_retained,originalWeightedRetained]
  let sourceData := actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat
  have packet : originalSevenPacket parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive sourceData candidate =
      originalSevenPacket parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive data candidate :=
    originalSevenPacket_same_sources parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive
      sourceData data candidate sameSources.symm
  dsimp only [originalSevenPacket] at seven packet
  have given := actualCartesianEquation_originalForceAndThird parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small coefficientSmall source flat data candidate equation sameSources allGrades
    (reindexPhysicalRow seven packet)
  intro radius inside angles
  change lower < radius ∧ radius < 1 at inside
  have actual := given radius inside angles
  have forceSame := funext (fun query : ℝ × ℝ => sameCartesianRawForce_reindexDatum
    parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state
    (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 sourceData)
    (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)
    (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate)
    seven packet radius ⟨inside.1.le,inside.2.le⟩ query.1 query.2)
  have projectedSame := congrArg (fun field => cartesianRadialMeanFree field angles) forceSame
  have thirdSame := sameCartesianThirdExpression_reindexDatum
    parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state
    (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 sourceData)
    (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)
    (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate)
    seven packet radius ⟨inside.1.le,inside.2.le⟩ angles.1 angles.2
  exact ⟨projectedSame.symm.trans actual.1,thirdSame.symm.trans actual.2⟩

end Grad.ActualCartesianWeakEquations
