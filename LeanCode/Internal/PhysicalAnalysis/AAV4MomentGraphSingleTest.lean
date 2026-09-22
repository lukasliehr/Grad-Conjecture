import AAV3VectorVariationalFormula

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularConverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.AnnularReconstruction Grad.GaugeCoefficients.Physical.WeightedTrace

theorem realScalar_pairing (scalar : ℝ) (test field : ComplexEuclidean 1) :
    inner ℂ ((scalar : ℂ) • test) field = inner ℂ test ((scalar : ℂ) • field) := by
  rw [inner_smul_left, inner_smul_right]
  simp

section Converse
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- Integration by parts proves the variational identity from the actual
uncorrected conormal derivative graph and its original outer boundary row. -/
theorem annularMomentGraph_single_test (field : annularEnergySpace lower length positive)
    (source : AnnularForcing lower) (mode : HighAnnularMode) (graph : WeightedRadialH1 1 lower)
    (value : collarH1Coordinate (ComplexEuclidean 1) lower 0
      (weightedToOrdinary 1 lower positive bounded.le graph) =
      annularUncorrectedFluxMoment parameters lower length positive lengthPositive widthHalf widthLength field source mode)
    (slope : collarH1Coordinate (ComplexEuclidean 1) lower 1
      (weightedToOrdinary 1 lower positive bounded.le graph) =
      annularUncorrectedFluxMomentRHS parameters lower length positive lengthPositive widthHalf widthLength field source mode)
    (outer : weightedRadialTrace 1 lower positive bounded 1 graph +
      (2 : ℝ) • weightedRadialTrace 1 lower positive bounded 1
        (annularModeRadialH1 lower length positive mode field) =
      -((Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) • source.2.2.2 mode))
    (test : complexSmoothRadialCore 1) (innerZero : test.val.1 lower = 0) :
    annularFormValue parameters lower length positive lengthPositive widthHalf widthLength field
      (annularEnergyCoreInto lower length positive (Finsupp.single mode test)) =
      annularFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source
        (annularEnergyCoreInto lower length positive (Finsupp.single mode test)) := by
  have parts := weightedRadial_vector_parts 1 lower positive bounded graph test
  rw [value, slope, innerZero, inner_zero_left, sub_zero] at parts
  change vectorCollarPairing lower test.val.2
      (annularUncorrectedFluxMoment parameters lower length positive lengthPositive widthHalf widthLength field source mode) +
    vectorCollarPairing lower test.val.1
      (annularUncorrectedFluxMomentRHS parameters lower length positive lengthPositive widthHalf widthLength field source mode) = _ at parts
  have outerPaired := congrArg (fun vector : ComplexEuclidean 1 => inner ℂ (test.val.1 1) vector) outer
  rw [inner_add_right, inner_neg_right] at outerPaired
  have boundary : inner ℂ ((Real.sqrt 2 : ℂ) • test.val.1 1)
      (annularEnergyOuter lower length positive field mode) =
      inner ℂ (test.val.1 1) ((2 : ℝ) • weightedRadialTrace 1 lower positive bounded 1
        (annularModeRadialH1 lower length positive mode field)) := by
    rw [annularEnergyOuter_eq_trace lower length positive bounded mode field]
    exact sqrtTwo_boundary_pairing _ _
  rw [annularForm_vector_moment, annularFunctional_vector_moment]
  dsimp only
  rw [boundary, realScalar_pairing]
  simp only [annularUncorrectedFluxMomentRHS, annularUncorrectedFluxMoment, map_add, map_sub] at parts ⊢
  linear_combination parts + outerPaired

end Converse
end Grad.AnnularConverse
