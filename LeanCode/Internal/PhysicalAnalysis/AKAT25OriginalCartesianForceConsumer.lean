import AKAT24OriginalCartesianSourceProjection
import AKAK20ActualCartesianSourceRadialConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open Set
open scoped ContDiff
namespace Grad.ActualCartesianEquations
open Grad.SourceCollarFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra
open Grad.AnnularHighGenerators Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow

open Grad.AnnularGeneralSourceRegularity Grad.ActualSmoothPhysicalField

open Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation

open Grad.ActualPolarEquations Grad.ActualPolarFlux Grad.SourceCollarFullSource

private theorem projectedPolarSourceTransport (first second : ℝ × ℝ → ℂ) (x y : ℂ) (angles : ℝ × ℝ)
    (radial : first=second) (tangential : x=y) :
    cartesianCovariantValue angles.1 (WithLp.toLp 2 ![removePolarMean first angles,x,0]) =
      cartesianCovariantValue angles.1 (WithLp.toLp 2 ![removePolarMean second angles,y,0]) := by
  cases radial
  cases tangential
  rfl

private theorem thirdSourceTransport (length : ℂ) (nonzero : length ≠ 0)
    (value source : ComplexEuclidean 1) (same : value=length⁻¹ • source) :
    length*value 0=source 0 := by
  rw [same,PiLp.smul_apply,smul_eq_mul,← mul_assoc,mul_inv_cancel₀ nonzero,one_mul]

/-- Literal original Cartesian force and toroidal equations for the SAME reconstructed fields and original source; all source and derivative fidelity is proved. -/
theorem actualCartesianEquation_originalForceAndThird
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
    cartesianRadialMeanFree (fun query => sameCartesianRawForce parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state
      (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)
      (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate) seven
      radius ⟨inside.1.le,inside.2.le⟩ query.1 query.2) angles =
      cartesianRadialMeanFree (literalCartesianPlanarSource parameters source radius (positive.le.trans inside.1.le) inside.2.le) angles ∧
    sameCartesianThirdExpression parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state
      (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)
      (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate) seven
      radius ⟨inside.1.le,inside.2.le⟩ angles.1 angles.2 =
      corePolarValue parameters (source 3) radius (positive.le.trans inside.1.le) inside.2.le angles 0 := by
  let force := sameKnownSourceCurves parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
    lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive source flat data sameSources 3
  intro radius inside angles
  have closedInside : radius ∈ Icc lower 1 := ⟨inside.1.le,inside.2.le⟩
  constructor
  · have given := actualCartesianEquation_projectedForce parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
      state small coefficientSmall source flat data candidate equation sameSources allGrades seven force radius inside angles
    apply given.trans
    have sourceSame := sameSevenKnown_literal parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
      lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive source flat data sameSources
      (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate) seven 0 radius closedInside angles
    change (seven.bulkUnit (0 : Fin 1) 4).fullField (lowerHalf.trans_lt (by norm_num)) (radius,angles) = _ at sourceSame
    have radialSame : (fun query => force.fullField (lowerHalf.trans_lt (by norm_num)) (radius,query) 0) =
        fun query => literalPrimitiveSource parameters length source radius (positive.le.trans inside.1.le) inside.2.le 0 query 0 := by
      funext query
      exact congrArg (fun value : ComplexEuclidean 1 => value 0)
        (sameKnownSource_fullField_literal parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
          lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive source flat data sameSources 0 force radius closedInside query)
    exact (projectedPolarSourceTransport _ _ _ _ angles radialSame
      (congrArg (fun value : ComplexEuclidean 1 => value 0) sourceSame)).trans
      (literalCartesianPlanarSource_projected parameters length source radius
        (positive.le.trans inside.1.le) inside.2.le angles).symm
  · have given := actualCartesianEquation_third parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
      state small coefficientSmall source flat data candidate equation sameSources allGrades seven radius inside angles
    apply given.trans
    have sourceSame := sameSevenKnown_literal parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
      lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive source flat data sameSources
      (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate) seven 1 radius closedInside angles
    change (seven.bulkUnit (0 : Fin 1) 6).fullField (lowerHalf.trans_lt (by norm_num)) (radius,angles) = _ at sourceSame
    exact thirdSourceTransport (length : ℂ) (Complex.ofReal_ne_zero.mpr lengthPositive.ne') _ _ sourceSame

end Grad.ActualCartesianEquations
