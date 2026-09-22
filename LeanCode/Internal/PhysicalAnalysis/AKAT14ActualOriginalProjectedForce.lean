import AKAT13SameProjectedCartesianForce
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

/-- The actual original coupled equation and original Cartesian source produce
the genuine SAME-field projected Cartesian force equation. No PDE, derivative
or field regularity is supplied as an extra premise. -/
theorem actualCartesianEquation_projectedForce
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
      (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data) (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate)))
      (force : SmoothLowPhysicalRow parameters lower positive
      (strongKnownBulk parameters lower positive (lowerHalf.trans (by norm_num)) (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data) 3)) :
    ∀ (radius : ℝ) (inside : radius ∈ Ioo lower 1) (angles : ℝ × ℝ),
    cartesianRadialMeanFree (fun query => sameCartesianRawForce parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state
      (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data) (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate) seven radius ⟨inside.1.le,inside.2.le⟩ query.1 query.2) angles =
      cartesianCovariantValue angles.1 (WithLp.toLp 2 ![
        removePolarMean (fun query => force.fullField (lowerHalf.trans_lt (by norm_num)) (radius,query) 0) angles,
        (seven.bulkUnit (0 : Fin 1) 4).fullField (lowerHalf.trans_lt (by norm_num)) (radius,angles) 0,0]) := by
  let sourceCurves := actualCartesianSourceCurves_of_sourceBlocks parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
    coefficientSmall lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive source flat data sameSources
  let third := actualThirdSourceCurves parameters lower positive (lowerHalf.trans_lt (by norm_num)) (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data) sourceCurves
  have smooth := actualCartesianEquation_phaseWeighted_radial parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
    state small coefficientSmall source flat data candidate equation sameSources allGrades
  intro radius inside angles
  apply sameCartesianProjectedForce_from_radial parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state
    (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data) (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate) seven allGrades smooth force radius inside ?_ angles
  intro query
  have actual := (originalEquation_physicalRadialPDE parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
    state small data candidate equation sourceCurves allGrades seven force third radius ⟨inside.1.le,inside.2.le⟩ query).2
  have same := samePhysical_fullField_eq
    ((SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 0).add force).meanFree
    ((seven.lowPhysicalCurves parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state 0).add force).meanFree
    (lowerHalf.trans_lt (by norm_num)) (Filter.Eventually.of_forall (fun _ _ => rfl)) radius ⟨inside.1.le,inside.2.le⟩ query
  rw [same] at actual
  exact actual

end Grad.ActualCartesianEquations
