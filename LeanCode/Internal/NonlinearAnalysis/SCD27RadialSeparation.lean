import SCD26FlatDivision
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState

def compactRadialTest (lower : ℝ) (test : ℝ → ℝ) (smooth : ContDiff ℝ ∞ test)
    (supported : tsupport test ⊆ Ioo lower 1) : RadialTest lower where
  value := test
  derivative := deriv test
  continuousValue := smooth.continuous
  continuousDerivative := (contDiff_infty_iff_deriv.mp smooth).2.continuous
  derivativeLaw := fun radius => (smooth.differentiable (by simp) radius).hasDerivAt
  lowerZero := by
    by_contra member
    have := supported (subset_closure member)
    exact (lt_irrefl lower) this.1
  upperZero := by
    by_contra member
    have := supported (subset_closure member)
    exact (lt_irrefl (1 : ℝ)) this.2

theorem radialPairing_general {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (test : ℝ → ℝ) (continuousTest : Continuous test)
    (vector : ComplexEuclidean dimension) (field : RadialL2 dimension lower) :
    radialPairing lower positive test continuousTest vector field =
      ∫ radius in Icc lower 1, test radius •
        (reciprocalRadialWeight lower (fun _ => 1) radius • inner ℂ vector (field radius)) := by
  change inner ℂ (radialTestLp lower positive test continuousTest vector) field = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(radial_test_memLp lower positive test continuousTest vector).coeFn_toLp]
    with radius representative
  change radialTestLp lower positive test continuousTest vector radius = _ at representative
  rw [representative, inner_smul_left_eq_smul, smul_smul]
  congr 1
  simp [reciprocalRadialWeight, div_eq_mul_inv]

/-- Scalar compact tests separate actual radial L2 values. The reciprocal
weight is continuous on each positive annulus, and never changes the norm. -/
theorem radialPairing_separates {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (field : RadialL2 dimension lower)
    (vanishes : ∀ (test : RadialTest lower) (vector : ComplexEuclidean dimension),
      radialPairing lower positive test.value test.continuousValue vector field = 0) :
    field = 0 := by
  have coordinateZero (coordinate : Fin dimension) :
      ∀ᵐ radius ∂volume.restrict (Icc lower 1), field radius coordinate = 0 := by
    let vector : ComplexEuclidean dimension := EuclideanSpace.single coordinate (1 : ℂ)
    let scalar : ℝ → ℂ := fun radius =>
      reciprocalRadialWeight lower (fun _ => 1) radius • inner ℂ vector (field radius)
    have locallyIntegrable : LocallyIntegrable scalar (volume.restrict (Icc lower 1)) :=
      LocallyIntegrable.continuous_smul
        (reciprocalRadialWeight_continuous lower positive (fun _ => 1) continuous_const)
        (((innerSL ℂ vector).comp_memLp field).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2))
    have zeroOn : ∀ᵐ radius ∂volume.restrict (Icc lower 1), radius ∈ Ioo lower 1 → scalar radius = 0 := by
      apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (locallyIntegrable.locallyIntegrableOn (Ioo lower 1))
      intro test smooth _compact supported
      rw [← radialPairing_general lower positive test smooth.continuous vector field]
      exact vanishes (compactRadialTest lower test smooth supported) vector
    have inside : ∀ᵐ radius ∂volume.restrict (Icc lower 1), radius ∈ Ioo lower 1 := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [zeroOn, inside] with radius zeroAt insideAt
    have zeroValue := zeroAt insideAt
    change reciprocalRadialWeight lower (fun _ => 1) radius • inner ℂ vector (field radius) = 0 at zeroValue
    have reciprocalNonzero : reciprocalRadialWeight lower (fun _ => 1) radius ≠ 0 := by
      unfold reciprocalRadialWeight
      exact div_ne_zero one_ne_zero (Real.sqrt_pos.2 (positive.trans_le (le_max_left _ _))).ne'
    have innerZero := (smul_eq_zero.mp zeroValue).resolve_left reciprocalNonzero
    simpa only [vector, EuclideanSpace.inner_single_left, map_one, one_mul] using innerZero
  apply Lp.ext
  filter_upwards [ae_all_iff.2 coordinateZero,
    Lp.coeFn_zero (ComplexEuclidean dimension) 2 (volume.restrict (Icc lower 1))]
    with radius coordinates zeroRepresentative
  rw [zeroRepresentative]
  apply PiLp.ext
  intro coordinate
  exact coordinates coordinate

theorem HasWeakRadialDerivative.unique {dimension : ℕ} {lower : ℝ} {positive : 0 < lower}
    {field first second : RadialL2 dimension lower}
    (firstLaw : HasWeakRadialDerivative lower positive field first)
    (secondLaw : HasWeakRadialDerivative lower positive field second) : first = second := by
  apply sub_eq_zero.mp
  apply radialPairing_separates lower positive
  intro test vector
  rw [map_sub, firstLaw test vector, secondLaw test vector, sub_self]

end Grad.SourceCollarDivision
