import AKBD30SameCorrectedPScalarRadial

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open Set
open scoped ContDiff
namespace Grad.ActualDeterminantEquations
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
open Grad.ActualCartesianEquations Grad.ActualCartesianDescent Grad.PhysicalFamily

/-- The genuine original coupled equation implies the literal signed Cartesian determinant equation for the SAME reconstructed field and unchanged Cartesian source. Every radial law, source correction, mean and derivative is proved. -/
theorem actualCartesianEquation_originalDeterminant
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
    removePolarMean (fun query => cartesianDeterminantDivergence length
      ((samePolarCofactorVector parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state seven).cartesianCovariant.cartesianField (lowerHalf.trans_lt (by norm_num)))
      (polarPlane (radius,query.1),query.2)) angles =
      corePolarValue parameters (source 2) radius (positive.le.trans inside.1.le) inside.2.le angles 0 := by
  let sourceCurves := actualCartesianSourceCurves_of_sourceBlocks parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
    coefficientSmall lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive source flat data sameSources
  let third := actualThirdSourceCurves parameters lower positive (lowerHalf.trans_lt (by norm_num))
    (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data) sourceCurves
  let forces := fun component : Fin 3 => sameKnownSourceCurves parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientSmall
    lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive source flat data sameSources (primitiveKnownSlot component)
  have smooth := actualCartesianEquation_phaseWeighted_radial parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
    state small coefficientSmall source flat data candidate equation sameSources allGrades
  intro radius inside angles
  apply actualOriginalCartesianDeterminant_from_radial parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state lengthPositive
    source flat data sameSources
    (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate)
    seven forces allGrades smooth third radius inside ?_ ?_ angles
  · intro query
    have actual := (originalEquation_physicalRadialPDE parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength
      state small data candidate equation sourceCurves allGrades seven (forces 0) third radius ⟨inside.1.le,inside.2.le⟩ query).2
    have same := samePhysical_fullField_eq
      ((SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 0).add (forces 0)).meanFree
      ((seven.lowPhysicalCurves parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state 0).add (forces 0)).meanFree
      (lowerHalf.trans_lt (by norm_num)) (Filter.Eventually.of_forall (fun _ _ => rfl)) radius ⟨inside.1.le,inside.2.le⟩ query
    exact same ▸ actual
  · intro query
    exact sameCorrectedP_scalarRadial_of_classical parameters length compact lower positive lowerHalf state lengthPositive
      (originalStrongWeightEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)
      (originalCoupledEquivalence parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive candidate)
      seven third radius inside query
      (actualCartesianEquation_correctedPRadial parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small coefficientSmall
        source flat data candidate equation sameSources allGrades seven third radius ⟨inside.1.le,inside.2.le⟩ query)

end Grad.ActualDeterminantEquations
