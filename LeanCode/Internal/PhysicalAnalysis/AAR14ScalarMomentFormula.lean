import AAR13ScalarVariationalTests

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem imaginarySymbol_star (symbol : ℝ) :
    starRingEnd ℂ (Complex.I * (symbol : ℂ)) = -(Complex.I * (symbol : ℂ)) := by
  simp

theorem weightedCurve_skew_pairing (lower : ℝ) (positive : 0 < lower)
    (symbol : ℂ) (skew : starRingEnd ℂ symbol = -symbol)
    (test : C(ℝ, ℝ)) (vector : ComplexEuclidean 1) (field : RadialL2 1 lower) :
    inner ℂ (symbol • weightedCurveComplex 1 lower (collarTestCurve test vector)) field =
      -collarPairing lower test vector (symbol • annularRadialMoment lower positive field) := by
  rw [inner_smul_left, skew, weightedCurve_test_moment, collarPairing_complex_smul, neg_mul]

theorem weightedCurve_leftScalar_pairing (lower : ℝ) (positive : 0 < lower)
    (coefficient test : C(ℝ, ℝ)) (vector : ComplexEuclidean 1) (field : RadialL2 1 lower) :
    inner ℂ (collarScalar 1 lower coefficient
      (weightedCurveComplex 1 lower (collarTestCurve test vector))) field =
    collarPairing lower test vector
      (collarScalar 1 lower coefficient (annularRadialMoment lower positive field)) :=
  (congrArg (fun value : RadialL2 1 lower => inner ℂ value field)
    (collarScalar_weightedCurve lower coefficient (collarTestCurve test vector))).trans
    (weightedCurve_scalar_pairing lower positive coefficient test vector field)

section Formula
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

theorem annularForm_scalar_moment (mode : HighAnnularMode)
    (profile : ℝ → ℝ) (smooth : ContDiff ℝ ∞ profile) (vector : ComplexEuclidean 1)
    (field : annularEnergySpace lower length positive) :
    let test : C(ℝ, ℝ) := ⟨profile, smooth.continuous⟩
    let derivative : C(ℝ, ℝ) := ⟨deriv profile, (contDiff_infty_iff_deriv.mp smooth).2.continuous⟩
    let H := annularRadialMoment lower positive
      (annularPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field mode)
    let U := annularRadialMoment lower positive (annularEnergyValue lower length positive field mode)
    annularFormValue parameters lower length positive lengthPositive widthHalf widthLength field
      (annularScalarTest lower length positive mode profile smooth vector) =
      collarPairing lower derivative vector H +
      collarPairing lower test vector
        (collarScalar 1 lower (annularPhaseCurve parameters mode.val.2) H +
          collarScalar 1 lower (annularPotentialCurve lower length positive mode) U) +
      inner ℂ ((Real.sqrt 2 : ℂ) • (profile 1 • vector)) (annularEnergyOuter lower length positive field mode) := by
  let core := smoothScalarRadialCore profile smooth vector
  let testMap : C(ℝ, ℝ) := ⟨profile, smooth.continuous⟩
  let derivativeMap : C(ℝ, ℝ) := ⟨deriv profile, (contDiff_infty_iff_deriv.mp smooth).2.continuous⟩
  let Hfield := annularPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field mode
  let phase := annularPhaseCurve parameters mode.val.2
  let potential := annularPotentialWeight lower length positive mode.val.1 mode.val.2
  have slopePair := (congrArg (fun curve : C(ℝ, ComplexEuclidean 1) =>
    inner ℂ (weightedCurveComplex 1 lower curve) Hfield)
    (smoothScalarRadialCore_slope_curve profile smooth vector)).trans
    (weightedCurve_test_moment lower positive derivativeMap vector Hfield)
  have phasePair := (congrArg (fun curve : C(ℝ, ComplexEuclidean 1) =>
    inner ℂ (collarScalar 1 lower phase (weightedCurveComplex 1 lower curve)) Hfield)
    (smoothScalarRadialCore_value_curve profile smooth vector)).trans
    (weightedCurve_leftScalar_pairing lower positive phase testMap vector Hfield)
  have massPair := (congrArg (fun curve : C(ℝ, ComplexEuclidean 1) =>
    inner ℂ (weightedCurveComplex 1 lower (continuousCurveWeight 1 potential curve))
      (annularEnergyMass lower length positive field mode))
    (smoothScalarRadialCore_value_curve profile smooth vector)).trans
    (annularMass_scalar_pairing lower length positive mode testMap vector field)
  have first := (inner_add_left (𝕜 := ℂ) (weightedCurveComplex 1 lower core.val.2)
    (collarScalar 1 lower phase (weightedCurveComplex 1 lower core.val.1)) Hfield).trans
    (congrArg₂ (fun first second : ℂ => first + second) slopePair phasePair)
  have combined := congrArg (fun value : ℂ => value +
      inner ℂ ((Real.sqrt 2 : ℂ) • (profile 1 • vector)) (annularEnergyOuter lower length positive field mode))
    (congrArg₂ (fun first second : ℂ => first + second) first massPair)
  have base := annularForm_single parameters lower length positive lengthPositive widthHalf widthLength mode core field
  refine base.trans (combined.trans ?_)
  dsimp only
  rw [map_add]
  abel

theorem annularFunctional_scalar_moment (bounded : lower < 1) (mode : HighAnnularMode)
    (profile : ℝ → ℝ) (smooth : ContDiff ℝ ∞ profile) (vector : ComplexEuclidean 1)
    (source : AnnularForcing lower) :
    let test : C(ℝ, ℝ) := ⟨profile, smooth.continuous⟩
    let derivative : C(ℝ, ℝ) := ⟨deriv profile, (contDiff_infty_iff_deriv.mp smooth).2.continuous⟩
    let F := annularRadialMoment lower positive (source.1 mode)
    let G := annularRadialMoment lower positive (source.2.1 mode)
    let H := annularRadialMoment lower positive (source.2.2.1 mode)
    annularFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source
      (annularScalarTest lower length positive mode profile smooth vector) =
      collarPairing lower derivative vector F +
      collarPairing lower test vector
        (collarScalar 1 lower (annularPhaseCurve parameters mode.val.2) F +
          collarScalar 1 lower (annularRadialCurve lower positive) F +
          annularDSymbol mode • G + annularCellSymbol length mode • H) -
      inner ℂ ((Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) •
        (profile 1 • vector)) (source.2.2.2 mode) := by
  dsimp only
  change annularFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source
    (annularEnergyCoreInto lower length positive (Finsupp.single mode (smoothScalarRadialCore profile smooth vector))) = _
  rw [annularFunctional_single, smoothScalarRadialCore_value_curve, smoothScalarRadialCore_slope_curve]
  rw [inner_add_left, inner_add_left, weightedCurve_test_moment lower positive,
    collarScalar_inner, collarScalar_inner, weightedCurve_test_moment lower positive, weightedCurve_test_moment lower positive,
    annularRadialMoment_scalar lower positive, annularRadialMoment_scalar lower positive,
    weightedCurve_skew_pairing lower positive (annularDSymbol mode) (imaginarySymbol_star _),
    weightedCurve_skew_pairing lower positive (annularCellSymbol length mode) (imaginarySymbol_star _)]
  simp only [map_add]
  simp only [collarTestCurve, ContinuousMap.coe_mk]
  abel

end Formula
end Grad.AnnularReconstruction
