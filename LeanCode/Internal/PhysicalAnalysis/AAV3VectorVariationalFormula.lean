import AAV2VectorMomentPairings

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularConverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.AnnularReconstruction Grad.GaugeCoefficients.Physical.WeightedTrace

section Formula
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem annularForm_vector_moment (mode : HighAnnularMode)
    (core : complexSmoothRadialCore 1)
    (field : annularEnergySpace lower length positive) :
    let H := annularRadialMoment lower positive
      (annularPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field mode)
    let U := annularRadialMoment lower positive (annularEnergyValue lower length positive field mode)
    annularFormValue parameters lower length positive lengthPositive widthHalf widthLength field
      (annularEnergyCoreInto lower length positive (Finsupp.single mode core)) =
      vectorCollarPairing lower core.val.2 H +
      vectorCollarPairing lower core.val.1
        (collarScalar 1 lower (annularPhaseCurve parameters mode.val.2) H +
          collarScalar 1 lower (annularPotentialCurve lower length positive mode) U) +
      inner ℂ ((Real.sqrt 2 : ℂ) • core.val.1 1) (annularEnergyOuter lower length positive field mode) := by
  let Hfield := annularPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field mode
  let phase := annularPhaseCurve parameters mode.val.2
  have slopePair := weightedCurve_vector_moment lower positive core.val.2 Hfield
  have phasePair := weightedCurve_vector_scalar lower positive phase core.val.1 Hfield
  have massPair := annularMass_vector_pairing lower length positive mode core.val.1 field
  have first := (inner_add_left (𝕜 := ℂ) (weightedCurveComplex 1 lower core.val.2)
    (collarScalar 1 lower phase (weightedCurveComplex 1 lower core.val.1)) Hfield).trans
    (congrArg₂ (fun first second : ℂ => first + second) slopePair phasePair)
  have combined := congrArg (fun value : ℂ => value +
      inner ℂ ((Real.sqrt 2 : ℂ) • core.val.1 1) (annularEnergyOuter lower length positive field mode))
    (congrArg₂ (fun first second : ℂ => first + second) first massPair)
  have base := annularForm_single parameters lower length positive lengthPositive widthHalf widthLength mode core field
  refine base.trans (combined.trans ?_)
  dsimp only
  rw [map_add]
  abel

theorem annularFunctional_vector_moment (bounded : lower < 1) (mode : HighAnnularMode)
    (core : complexSmoothRadialCore 1)
    (source : AnnularForcing lower) :
    let F := annularRadialMoment lower positive (source.1 mode)
    let G := annularRadialMoment lower positive (source.2.1 mode)
    let H := annularRadialMoment lower positive (source.2.2.1 mode)
    annularFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source
      (annularEnergyCoreInto lower length positive (Finsupp.single mode core)) =
      vectorCollarPairing lower core.val.2 F +
      vectorCollarPairing lower core.val.1
        (collarScalar 1 lower (annularPhaseCurve parameters mode.val.2) F +
          collarScalar 1 lower (annularRadialCurve lower positive) F +
          annularDSymbol mode • G + annularCellSymbol length mode • H) -
      inner ℂ ((Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) •
        core.val.1 1) (source.2.2.2 mode) := by
  dsimp only
  rw [annularFunctional_single]
  rw [inner_add_left, inner_add_left, weightedCurve_vector_moment lower positive,
    collarScalar_inner, collarScalar_inner, weightedCurve_vector_moment lower positive, weightedCurve_vector_moment lower positive,
    annularRadialMoment_scalar lower positive, annularRadialMoment_scalar lower positive,
    weightedCurve_vector_skew lower positive (annularDSymbol mode) (imaginarySymbol_star _),
    weightedCurve_vector_skew lower positive (annularCellSymbol length mode) (imaginarySymbol_star _)]
  simp only [map_add]
  abel

end Formula
end Grad.AnnularConverse
