import ANR26OrdinaryRadialPairing

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.WeightedTrace

def radialRadiusCurve : C(ℝ, ℝ) := ⟨id, continuous_id⟩

/-- A continuous extension of the literal m²/r potential on this collar. -/
def radialPotentialCurve (lower : ℝ) (positive : 0 < lower) (mode : ℤ) : C(ℝ, ℝ) :=
  ⟨fun radius => (mode : ℝ) ^ 2 / max lower radius,
    continuous_const.div (continuous_const.max continuous_id)
      (fun radius => (positive.trans_le (le_max_left lower radius)).ne')⟩

theorem radialPotentialCurve_literal (lower : ℝ) (positive : 0 < lower) (mode : ℤ)
    (radius : ℝ) (inside : lower ≤ radius) :
    radialPotentialCurve lower positive mode radius = (mode : ℝ) ^ 2 / radius := by
  change (mode : ℝ) ^ 2 / max lower radius = _
  rw [max_eq_right inside]

theorem collarPairing_test_congr (dimension : ℕ) (lower : ℝ) (first second : C(ℝ, ℝ))
    (same : ∀ radius ∈ Icc lower 1, first radius = second radius)
    (vector : ComplexEuclidean dimension) (field : CollarL2 (ComplexEuclidean dimension) lower) :
    collarPairing lower first vector field = collarPairing lower second vector field := by
  rw [collarPairing_integral, collarPairing_integral]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
  rw [same radius inside]

/-- The first-order flux law follows from the second-order distribution
equation and the already established genuine first weak derivative. -/
theorem radial_secondTest_to_flux (lower : ℝ) (positive : 0 < lower) (mode : ℤ)
    (value derivative laplacian : CollarL2 (ComplexEuclidean 1) lower)
    (weak : CollarWeakDerivative lower value derivative)
    (equation : ∀ (test : ℝ → ℝ) (smooth : ContDiff ℝ ∞ test)
      (supported : tsupport test ⊆ Ioo lower 1) (vector : ComplexEuclidean 1),
      collarPairing lower ⟨fun radius => radius * radialTestOperator mode test radius,
        continuous_id.mul (radialTestOperator_smooth mode test smooth
          (collar_supported_inside lower positive test supported)).continuous⟩ vector value =
      collarPairing lower ⟨fun radius => radius * test radius,
        continuous_id.mul smooth.continuous⟩ vector laplacian) :
    CompactWeakDerivative 1 lower
      (collarScalar 1 lower radialRadiusCurve derivative)
      (collarScalar 1 lower (radialPotentialCurve lower positive mode) value +
        collarScalar 1 lower radialRadiusCurve laplacian) := by
  intro test smooth _compact supported vector
  let firstSmooth := (contDiff_infty_iff_deriv.mp smooth).2
  let auxiliary : ℝ → ℝ := fun radius => radius * deriv test radius
  have auxiliarySmooth : ContDiff ℝ ∞ auxiliary := contDiff_id.mul firstSmooth
  have auxiliarySupport : tsupport auxiliary ⊆ Ioo lower 1 :=
    tsupport_mul_subset_right.trans (tsupport_deriv_subset.trans supported)
  have auxiliaryDerivative (radius : ℝ) :
      deriv auxiliary radius = deriv test radius + radius * deriv (deriv test) radius := by
    have identity := ((hasDerivAt_id radius).mul
      ((firstSmooth.differentiable (by simp)) radius).hasDerivAt).deriv
    have functions : (id * deriv test : ℝ → ℝ) = auxiliary := rfl
    rw [functions] at identity
    simpa only [one_mul, id_eq] using identity
  let testMap : C(ℝ, ℝ) := ⟨test, smooth.continuous⟩
  let auxiliaryMap : C(ℝ, ℝ) := ⟨auxiliary, auxiliarySmooth.continuous⟩
  let auxiliaryDeriv : C(ℝ, ℝ) := ⟨deriv auxiliary, (contDiff_infty_iff_deriv.mp auxiliarySmooth).2.continuous⟩
  let potentialTest : C(ℝ, ℝ) := testMap * radialPotentialCurve lower positive mode
  let operatorMap : C(ℝ, ℝ) := ⟨fun radius => radius * radialTestOperator mode test radius,
    continuous_id.mul (radialTestOperator_smooth mode test smooth
      (collar_supported_inside lower positive test supported)).continuous⟩
  have operatorEqual : ∀ radius ∈ Icc lower 1, operatorMap radius = (auxiliaryDeriv - potentialTest) radius := by
    intro radius inside
    change radius * radialTestOperator mode test radius = deriv auxiliary radius -
      test radius * radialPotentialCurve lower positive mode radius
    rw [auxiliaryDerivative, radialPotentialCurve_literal lower positive mode radius inside.1]
    unfold radialTestOperator
    field_simp [(positive.trans_le inside.1).ne']
    ring
  have operatorPair := collarPairing_test_congr 1 lower operatorMap (auxiliaryDeriv - potentialTest)
    operatorEqual vector value
  have weakLaw : collarPairing lower auxiliaryMap vector derivative =
      -collarPairing lower auxiliaryDeriv vector value :=
    weak (collarCompactTest lower auxiliary auxiliarySmooth auxiliarySupport) vector
  have secondLaw := equation test smooth supported vector
  change collarPairing lower operatorMap vector value =
    collarPairing lower (radialRadiusCurve * testMap) vector laplacian at secondLaw
  rw [operatorPair, collarPairing_test_sub] at secondLaw
  rw [map_add, collarScalar_pairing, collarScalar_pairing, collarScalar_pairing]
  have product : testMap * radialRadiusCurve = radialRadiusCurve * testMap := mul_comm _ _
  have auxiliaryProduct : (⟨deriv test, firstSmooth.continuous⟩ : C(ℝ, ℝ)) * radialRadiusCurve = auxiliaryMap := by
    apply ContinuousMap.ext
    intro radius
    exact mul_comm _ _
  change collarPairing lower potentialTest vector value +
    collarPairing lower (testMap * radialRadiusCurve) vector laplacian =
      -collarPairing lower (⟨deriv test, firstSmooth.continuous⟩ * radialRadiusCurve) vector derivative
  rw [product, auxiliaryProduct]
  linear_combination -secondLaw + weakLaw

end Grad.CircularHighRegularity
