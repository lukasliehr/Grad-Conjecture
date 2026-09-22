import AKAK19OriginalEquationRadialPDE

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open Set
open scoped ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra
open Grad.AnnularHighGenerators Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow

open Grad.AnnularGeneralSourceRegularity Grad.ActualSmoothPhysicalField

open Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation

/-- The actual Cartesian source allocation and actual original equation
supply both genuine radial PDEs for the same reconstructed field. Every
source/row regularity input is constructed from accepted actual APIs. -/
theorem actualCartesianEquation_physicalRadialPDE
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
        (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate) weighted) :
    ∃ (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data) (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate)))
      (force : SmoothLowPhysicalRow parameters lower positive
      (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data) 3))
      (third : SmoothLowPhysicalRow parameters lower positive
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)).ofLp.1.ofLp.2),
      ∀ (radius : ℝ) (_inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ),
    HasDerivWithinAt
      (fun current => originalPhysicalComponentField parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate) 0 (current,angles))
      (determinantPhysicalRHS length radius
        (actualDeterminantFields parameters length compact lower positive lowerHalf lengthPositive state (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data) (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate) seven third radius) angles)
      (Icc lower 1) radius ∧
    HasDerivWithinAt
      (fun current => originalPhysicalComponentField parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate) 1 (current,angles))
      (((SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 0).add force).meanFree.fullField
        (lowerHalf.trans_lt (by norm_num)) (radius,angles)) (Icc lower 1) radius := by
  let curves := actualCartesianSourceCurves_of_sourceBlocks parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
    coefficientSmall lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive source flat data sameSources
  have actual := actualCartesianEquation_fullSeven_smooth parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small coefficientSmall source flat data candidate equation sameSources allGrades
  let seven := SmoothLowPhysicalRow.of_shifted parameters lower positive
    (Grad.AnnularRestriction.originalSevenPacket parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive data candidate)
    actual.choose actual.choose_spec.1 actual.choose_spec.2
  let force := ActualSourceRadialCurves.forceRow parameters lower positive lowerHalf (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data) curves
  let third := actualThirdSourceCurves parameters lower positive (lowerHalf.trans_lt (by norm_num)) (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data) curves
  refine ⟨seven,force,third,?_⟩
  intro radius inside angles
  exact originalEquation_physicalRadialPDE parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
    state small data candidate equation curves allGrades seven force third radius inside angles

end Grad.ActualPolarEquations
