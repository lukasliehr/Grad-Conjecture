import AKBE7ActualObservedCartesianEquations
import AKBD31ActualOriginalCartesianDeterminant

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.ActualCartesianWeakEquations
open Grad.ActualDeterminantEquations Grad.ActualCartesianDescent Grad.PhysicalFamily
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


private theorem reindexPhysicalRow_cofactorCartesian
    (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    {first second : DivisionRow 7 lower} (curves : SmoothLowPhysicalRow parameters lower positive first)
    (same : first = second) :
    (samePolarCofactorVector parameters length compact lower positive bounded state
      (reindexPhysicalRow curves same)).cartesianCovariant.cartesianField bounded =
      (samePolarCofactorVector parameters length compact lower positive bounded state curves).cartesianCovariant.cartesianField bounded := by
  cases same
  rfl

include member sameSources allGrades small in
/-- The genuine determinant law for the SAME observed canonical seven packet.
Changing its incoming-data label leaves the actual reconstructed flux unchanged. -/
theorem actualObserved_originalDeterminant :
    ∀ (radius : ℝ) (inside : radius ∈ Ioo lower 1) (angles : ℝ × ℝ),
    removePolarMean (fun query => cartesianDeterminantDivergence length
      ((samePolarCofactorVector parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state seven).cartesianCovariant.cartesianField (lowerHalf.trans_lt (by norm_num)))
      (polarPlane (radius,query.1),query.2)) angles =
      corePolarValue parameters (source 2) radius (positive.le.trans inside.1.le) inside.2.le angles 0 := by
  obtain ⟨⟨data,candidate⟩,equation,rfl⟩ := member
  simp only [originalFiveBlockObservation_retained] at seven
  let sourceData := actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall lower positive (lowerHalf.trans_lt (by norm_num)) 0 source flat
  have packet : originalSevenPacket parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive sourceData candidate =
      originalSevenPacket parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive data candidate :=
    originalSevenPacket_same_sources parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive
      sourceData data candidate sameSources.symm
  dsimp only [originalSevenPacket] at seven packet
  have given := actualCartesianEquation_originalDeterminant parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small coefficientSmall source flat data candidate equation sameSources allGrades
    (reindexPhysicalRow seven packet)
  intro radius inside angles
  have sameField := reindexPhysicalRow_cofactorCartesian parameters length compact lower positive
    (lowerHalf.trans_lt (by norm_num)) state seven packet
  have sameDiv := congrArg (fun field => removePolarMean (fun query =>
    cartesianDeterminantDivergence length field (polarPlane (radius,query.1),query.2)) angles) sameField
  exact sameDiv.symm.trans (given radius inside angles)

end Grad.ActualCartesianWeakEquations
